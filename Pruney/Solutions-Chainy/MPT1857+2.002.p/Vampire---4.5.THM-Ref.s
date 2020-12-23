%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 (1954 expanded)
%              Number of leaves         :   17 ( 726 expanded)
%              Depth                    :   36
%              Number of atoms          :  523 (13397 expanded)
%              Number of equality atoms :   68 (3201 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(subsumption_resolution,[],[f315,f69])).

fof(f69,plain,(
    ~ v2_tex_2(sK2,sK1) ),
    inference(forward_demodulation,[],[f46,f44])).

fof(f44,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v2_tex_2(sK3,sK1)
    & v2_tex_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tex_2(X3,X1)
                    & v2_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tex_2(X3,X1)
                & v2_tex_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tex_2(X3,sK1)
              & v2_tex_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tex_2(X3,sK1)
            & v2_tex_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ v2_tex_2(X3,sK1)
          & v2_tex_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ v2_tex_2(X3,sK1)
        & v2_tex_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ~ v2_tex_2(sK3,sK1)
      & v2_tex_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

fof(f46,plain,(
    ~ v2_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f315,plain,(
    v2_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f312,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK2,sK1) ),
    inference(resolution,[],[f308,f227])).

fof(f227,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X1,sK1) ) ),
    inference(forward_demodulation,[],[f226,f129])).

fof(f129,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f128,f92])).

fof(f92,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f89,f83])).

fof(f83,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X1,sK1) ) ),
    inference(forward_demodulation,[],[f82,f43])).

fof(f43,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(X1,sK1) ) ),
    inference(resolution,[],[f60,f40])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f89,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f88,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f86,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f128,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ m1_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f127,f40])).

fof(f127,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f124,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f51,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f124,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(resolution,[],[f120,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f120,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f119,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK1))
      | r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f117,f64])).

fof(f117,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f114,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f110,f103])).

fof(f103,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f91,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f60,f39])).

fof(f91,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f90,f43])).

fof(f90,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f88,f40])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f226,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_tex_2(X1,sK1) ) ),
    inference(forward_demodulation,[],[f225,f129])).

fof(f225,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_tex_2(X1,sK1) ) ),
    inference(resolution,[],[f56,f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
                    & v3_pre_topc(sK5(X0,X1,X4),X0)
                    & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
        & v3_pre_topc(sK5(X0,X1,X4),X0)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f308,plain,(
    ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f307,f183])).

fof(f183,plain,(
    r1_tarski(sK4(sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f177,f69])).

fof(f177,plain,
    ( r1_tarski(sK4(sK1,sK2),sK2)
    | v2_tex_2(sK2,sK1) ),
    inference(resolution,[],[f162,f41])).

fof(f162,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK4(sK1,X1),X1)
      | v2_tex_2(X1,sK1) ) ),
    inference(forward_demodulation,[],[f161,f129])).

fof(f161,plain,(
    ! [X1] :
      ( r1_tarski(sK4(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_tex_2(X1,sK1) ) ),
    inference(resolution,[],[f57,f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f307,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK4(sK1,sK2),sK2) ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK4(sK1,sK2),sK2) ),
    inference(resolution,[],[f302,f249])).

fof(f249,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f248,f39])).

fof(f248,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f247,f41])).

fof(f247,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f53,f45])).

fof(f45,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f302,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f298,f183])).

fof(f298,plain,
    ( ~ r1_tarski(sK4(sK1,sK2),sK2)
    | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f295,f284])).

fof(f284,plain,
    ( ~ v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f283,f41])).

fof(f283,plain,
    ( ~ v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f282,f69])).

fof(f282,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,
    ( sK4(sK1,sK2) != sK4(sK1,sK2)
    | v2_tex_2(sK2,sK1)
    | ~ v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f257,f276])).

fof(f276,plain,(
    sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f275,f69])).

fof(f275,plain,
    ( sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2)))
    | v2_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f272,f41])).

fof(f272,plain,
    ( sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK2,sK1) ),
    inference(resolution,[],[f263,f227])).

fof(f263,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2))) ),
    inference(resolution,[],[f260,f183])).

fof(f260,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f259,f39])).

fof(f259,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,X0)) = X0
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f258,f41])).

fof(f258,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,X0)) = X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f257,plain,(
    ! [X0,X1] :
      ( sK4(sK1,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1)
      | v2_tex_2(X0,sK1)
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f256,f40])).

fof(f256,plain,(
    ! [X0,X1] :
      ( sK4(sK1,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1)
      | v2_tex_2(X0,sK1)
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f58,f129])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f295,plain,(
    ! [X2] :
      ( v3_pre_topc(sK5(sK0,sK2,X2),sK1)
      | ~ r1_tarski(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f294,f249])).

fof(f294,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK5(sK0,sK2,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK2)
      | v3_pre_topc(sK5(sK0,sK2,X2),sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f290,f129])).

fof(f290,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK2)
      | ~ m1_subset_1(sK5(sK0,sK2,X2),k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(sK5(sK0,sK2,X2),sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f287,f103])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ r1_tarski(X0,sK2)
      | ~ m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(sK5(sK0,sK2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f286,f39])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK2)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(sK5(sK0,sK2,X0),X1)
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f285,f41])).

fof(f285,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(sK5(sK0,sK2,X0),X1)
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f246,f45])).

fof(f246,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(sK5(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X3)))
      | v3_pre_topc(sK5(X2,X1,X0),X3)
      | ~ m1_pre_topc(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v2_tex_2(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(sK5(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X3)))
      | v3_pre_topc(sK5(X2,X1,X0),X3)
      | ~ m1_pre_topc(X3,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f54,f236])).

fof(f236,plain,(
    ! [X2,X0,X3] :
      ( ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f66,f52])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK5(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:44:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (421)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (402)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (407)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (406)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (422)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (413)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (424)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (404)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (414)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (402)Refutation not found, incomplete strategy% (402)------------------------------
% 0.21/0.52  % (402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (408)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (416)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (411)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (427)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (426)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (402)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (402)Memory used [KB]: 10618
% 0.21/0.52  % (402)Time elapsed: 0.105 s
% 0.21/0.52  % (402)------------------------------
% 0.21/0.52  % (402)------------------------------
% 0.21/0.52  % (409)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (418)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (415)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (423)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (415)Refutation not found, incomplete strategy% (415)------------------------------
% 0.21/0.53  % (415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (415)Memory used [KB]: 6268
% 0.21/0.53  % (415)Time elapsed: 0.120 s
% 0.21/0.53  % (415)------------------------------
% 0.21/0.53  % (415)------------------------------
% 0.21/0.53  % (412)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (405)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (403)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (417)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (420)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (410)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (408)Refutation not found, incomplete strategy% (408)------------------------------
% 0.21/0.54  % (408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (408)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (408)Memory used [KB]: 10618
% 0.21/0.54  % (408)Time elapsed: 0.082 s
% 0.21/0.54  % (408)------------------------------
% 0.21/0.54  % (408)------------------------------
% 0.21/0.54  % (425)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (423)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f316,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f315,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ~v2_tex_2(sK2,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f46,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    sK2 = sK3),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    (((~v2_tex_2(sK3,sK1) & v2_tex_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f28,f27,f26,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tex_2(X3,sK1) & v2_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ? [X2] : (? [X3] : (~v2_tex_2(X3,sK1) & v2_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~v2_tex_2(X3,sK1) & v2_tex_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ? [X3] : (~v2_tex_2(X3,sK1) & v2_tex_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => (~v2_tex_2(sK3,sK1) & v2_tex_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tex_2(X3,X1) & (v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f11])).
% 0.21/0.55  fof(f11,conjecture,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ~v2_tex_2(sK3,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f315,plain,(
% 0.21/0.55    v2_tex_2(sK2,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f312,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f312,plain,(
% 0.21/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK2,sK1)),
% 0.21/0.55    inference(resolution,[],[f308,f227])).
% 0.21/0.55  fof(f227,plain,(
% 0.21/0.55    ( ! [X1] : (m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f226,f129])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f128,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    m1_pre_topc(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f89,f83])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X1,sK1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f82,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X1,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f60,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    l1_pre_topc(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(resolution,[],[f88,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    l1_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(resolution,[],[f86,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f48,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    u1_struct_0(sK0) = u1_struct_0(sK1) | ~m1_pre_topc(sK0,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f127,f40])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    u1_struct_0(sK0) = u1_struct_0(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f124,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f51,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.55    inference(resolution,[],[f120,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.55    inference(resolution,[],[f119,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK1)) | r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.21/0.55    inference(resolution,[],[f117,f64])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,u1_struct_0(sK1))) )),
% 0.21/0.55    inference(resolution,[],[f114,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(resolution,[],[f110,f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    m1_pre_topc(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f91,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f60,f39])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(forward_demodulation,[],[f90,f43])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(resolution,[],[f88,f40])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(resolution,[],[f52,f39])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    ( ! [X1] : (m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v2_tex_2(X1,sK1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f225,f129])).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    ( ! [X1] : (m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v2_tex_2(X1,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f56,f40])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v3_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v3_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(rectify,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.21/0.55  fof(f308,plain,(
% 0.21/0.55    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f307,f183])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    r1_tarski(sK4(sK1,sK2),sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f177,f69])).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    r1_tarski(sK4(sK1,sK2),sK2) | v2_tex_2(sK2,sK1)),
% 0.21/0.55    inference(resolution,[],[f162,f41])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK4(sK1,X1),X1) | v2_tex_2(X1,sK1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f161,f129])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(sK4(sK1,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v2_tex_2(X1,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f57,f40])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | r1_tarski(sK4(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f307,plain,(
% 0.21/0.55    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK1,sK2),sK2)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f304])).
% 0.21/0.55  fof(f304,plain,(
% 0.21/0.55    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(sK1,sK2),sK2)),
% 0.21/0.55    inference(resolution,[],[f302,f249])).
% 0.21/0.55  fof(f249,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f248,f39])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f247,f41])).
% 0.21/0.55  fof(f247,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f53,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    v2_tex_2(sK2,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~v2_tex_2(X1,X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f302,plain,(
% 0.21/0.55    ~m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f298,f183])).
% 0.21/0.55  fof(f298,plain,(
% 0.21/0.55    ~r1_tarski(sK4(sK1,sK2),sK2) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(resolution,[],[f295,f284])).
% 0.21/0.55  fof(f284,plain,(
% 0.21/0.55    ~v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1) | ~m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f283,f41])).
% 0.21/0.55  fof(f283,plain,(
% 0.21/0.55    ~v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1) | ~m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f282,f69])).
% 0.21/0.55  fof(f282,plain,(
% 0.21/0.55    v2_tex_2(sK2,sK1) | ~v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1) | ~m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f281])).
% 0.21/0.55  fof(f281,plain,(
% 0.21/0.55    sK4(sK1,sK2) != sK4(sK1,sK2) | v2_tex_2(sK2,sK1) | ~v3_pre_topc(sK5(sK0,sK2,sK4(sK1,sK2)),sK1) | ~m1_subset_1(sK5(sK0,sK2,sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(superposition,[],[f257,f276])).
% 0.21/0.55  fof(f276,plain,(
% 0.21/0.55    sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f275,f69])).
% 0.21/0.55  fof(f275,plain,(
% 0.21/0.55    sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2))) | v2_tex_2(sK2,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f272,f41])).
% 0.21/0.55  fof(f272,plain,(
% 0.21/0.55    sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK2,sK1)),
% 0.21/0.55    inference(resolution,[],[f263,f227])).
% 0.21/0.55  fof(f263,plain,(
% 0.21/0.55    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | sK4(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,sK4(sK1,sK2)))),
% 0.21/0.55    inference(resolution,[],[f260,f183])).
% 0.21/0.55  fof(f260,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,X0)) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f259,f39])).
% 0.21/0.55  fof(f259,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,X0)) = X0 | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f258,f41])).
% 0.21/0.55  fof(f258,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK2,sK5(sK0,sK2,X0)) = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f55,f45])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~v2_tex_2(X1,X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f257,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sK4(sK1,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1) | v2_tex_2(X0,sK1) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f256,f40])).
% 0.21/0.55  fof(f256,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sK4(sK1,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1) | v2_tex_2(X0,sK1) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK1)) )),
% 0.21/0.55    inference(superposition,[],[f58,f129])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | v2_tex_2(X1,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f295,plain,(
% 0.21/0.55    ( ! [X2] : (v3_pre_topc(sK5(sK0,sK2,X2),sK1) | ~r1_tarski(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f294,f249])).
% 0.21/0.55  fof(f294,plain,(
% 0.21/0.55    ( ! [X2] : (~m1_subset_1(sK5(sK0,sK2,X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK2) | v3_pre_topc(sK5(sK0,sK2,X2),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f290,f129])).
% 0.21/0.55  fof(f290,plain,(
% 0.21/0.55    ( ! [X2] : (~r1_tarski(X2,sK2) | ~m1_subset_1(sK5(sK0,sK2,X2),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK5(sK0,sK2,X2),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(resolution,[],[f287,f103])).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~r1_tarski(X0,sK2) | ~m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(sK5(sK0,sK2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f286,f39])).
% 0.21/0.55  fof(f286,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(sK5(sK0,sK2,X0),X1) | ~m1_pre_topc(X1,sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f285,f41])).
% 0.21/0.55  fof(f285,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK5(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(sK5(sK0,sK2,X0),X1) | ~m1_pre_topc(X1,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f246,f45])).
% 0.21/0.55  fof(f246,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(sK5(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X3))) | v3_pre_topc(sK5(X2,X1,X0),X3) | ~m1_pre_topc(X3,X2)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f245])).
% 0.21/0.55  fof(f245,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) | ~v2_tex_2(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(sK5(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X3))) | v3_pre_topc(sK5(X2,X1,X0),X3) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.55    inference(resolution,[],[f54,f236])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    ( ! [X2,X0,X3] : (~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f66,f52])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (v3_pre_topc(sK5(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (423)------------------------------
% 0.21/0.55  % (423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (423)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (423)Memory used [KB]: 6396
% 0.21/0.55  % (423)Time elapsed: 0.126 s
% 0.21/0.55  % (423)------------------------------
% 0.21/0.55  % (423)------------------------------
% 0.21/0.55  % (409)Refutation not found, incomplete strategy% (409)------------------------------
% 0.21/0.55  % (409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (409)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (409)Memory used [KB]: 1791
% 0.21/0.55  % (409)Time elapsed: 0.140 s
% 0.21/0.55  % (409)------------------------------
% 0.21/0.55  % (409)------------------------------
% 0.21/0.56  % (401)Success in time 0.188 s
%------------------------------------------------------------------------------
