%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 955 expanded)
%              Number of leaves         :   10 ( 387 expanded)
%              Depth                    :   36
%              Number of atoms          :  463 (8137 expanded)
%              Number of equality atoms :   84 (2136 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f146,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v3_tex_2(sK3,sK1)
    & v3_tex_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_tex_2(X3,X1)
                    & v3_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_tex_2(X3,X1)
                & v3_tex_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_tex_2(X3,sK1)
              & v3_tex_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_tex_2(X3,sK1)
            & v3_tex_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ v3_tex_2(X3,sK1)
          & v3_tex_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ~ v3_tex_2(X3,sK1)
        & v3_tex_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ~ v3_tex_2(sK3,sK1)
      & v3_tex_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v3_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v3_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v3_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tex_2)).

fof(f146,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f145,f111])).

fof(f111,plain,(
    v2_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f110,f29])).

fof(f29,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f110,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f108,f45])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f28,f30])).

fof(f30,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f108,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_tex_2(sK2,sK1) ),
    inference(resolution,[],[f105,f26])).

fof(f26,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f105,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | v2_tex_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f103,f27])).

fof(f103,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(sK2,X0) ) ),
    inference(resolution,[],[f99,f48])).

fof(f48,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f47,f25])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f46,f27])).

fof(f46,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    v3_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK4(X0,X1) != X1
                & r1_tarski(X1,sK4(X0,X1))
                & v2_tex_2(sK4(X0,X1),X0)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) != X1
        & r1_tarski(X1,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(X0,X1) ) ),
    inference(resolution,[],[f43,f25])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X3,X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(X3,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_tex_2(X3,X1)
      | ~ v2_tex_2(X2,X0)
      | X2 != X3
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f145,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f144,f44])).

fof(f44,plain,(
    ~ v3_tex_2(sK2,sK1) ),
    inference(forward_demodulation,[],[f32,f30])).

fof(f32,plain,(
    ~ v3_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f144,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f143,f96])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK1)
      | ~ v2_tex_2(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f95,f26])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK1)
      | ~ v2_tex_2(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f37,f55])).

fof(f55,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f53])).

fof(f53,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f51,f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f49,f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f41,f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f143,plain,(
    ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f142,f26])).

fof(f142,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f141,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f140,f111])).

fof(f140,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f139,f44])).

fof(f139,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK2,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f138,f25])).

fof(f138,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK2,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f137,f27])).

fof(f137,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK2,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f135,f31])).

fof(f135,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tex_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK2,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f134,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(sK4(X1,X0),X2)
      | ~ m1_subset_1(sK4(X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_tex_2(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v3_tex_2(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f97,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sK4(X1,X0) = X0
      | ~ v2_tex_2(sK4(X1,X0),X2)
      | ~ m1_subset_1(sK4(X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_tex_2(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v3_tex_2(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK4(X0,X1))
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X1,X3)
      | X1 = X3
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f134,plain,(
    v2_tex_2(sK4(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f133,f27])).

fof(f133,plain,
    ( v2_tex_2(sK4(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f132,f111])).

fof(f132,plain,
    ( v2_tex_2(sK4(sK1,sK2),sK0)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f131,f44])).

fof(f131,plain,
    ( v2_tex_2(sK4(sK1,sK2),sK0)
    | v3_tex_2(sK2,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f128,f96])).

fof(f128,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK4(sK1,sK2),sK0) ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v2_tex_2(sK4(sK1,sK2),sK0) ),
    inference(resolution,[],[f122,f25])).

fof(f122,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | v2_tex_2(sK4(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f121,f27])).

fof(f121,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(sK4(sK1,sK2),X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(sK4(sK1,sK2),X0)
      | v3_tex_2(sK2,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f116,f111])).

fof(f116,plain,(
    ! [X2,X1] :
      ( ~ v2_tex_2(X2,sK1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(sK4(sK1,X2),X1)
      | v3_tex_2(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f115,f96])).

fof(f115,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(sK4(sK1,X2),X1)
      | v3_tex_2(X2,sK1)
      | ~ v2_tex_2(X2,sK1) ) ),
    inference(forward_demodulation,[],[f114,f55])).

fof(f114,plain,(
    ! [X2,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(sK4(sK1,X2),X1)
      | v3_tex_2(X2,sK1)
      | ~ v2_tex_2(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f113,f26])).

fof(f113,plain,(
    ! [X2,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(sK4(sK1,X2),X1)
      | v3_tex_2(X2,sK1)
      | ~ v2_tex_2(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f102,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    ! [X2,X3] :
      ( ~ v2_tex_2(X2,sK1)
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v2_tex_2(X2,X3) ) ),
    inference(forward_demodulation,[],[f101,f55])).

fof(f101,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ v2_tex_2(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(X3)
      | v2_tex_2(X2,X3) ) ),
    inference(forward_demodulation,[],[f100,f29])).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ v2_tex_2(X2,sK1)
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(X3)
      | v2_tex_2(X2,X3) ) ),
    inference(resolution,[],[f43,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:26:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (27554)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (27554)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f146,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    (((~v3_tex_2(sK3,sK1) & v3_tex_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v3_tex_2(X3,sK1) & v3_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X2] : (? [X3] : (~v3_tex_2(X3,sK1) & v3_tex_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~v3_tex_2(X3,sK1) & v3_tex_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X3] : (~v3_tex_2(X3,sK1) & v3_tex_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => (~v3_tex_2(sK3,sK1) & v3_tex_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v3_tex_2(X3,X1) & (v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f5])).
% 0.20/0.49  fof(f5,conjecture,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tex_2)).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f145,f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    v2_tex_2(sK2,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | v2_tex_2(sK2,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f108,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.49    inference(forward_demodulation,[],[f28,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    sK2 = sK3),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | v2_tex_2(sK2,sK1)),
% 0.20/0.49    inference(resolution,[],[f105,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    l1_pre_topc(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v2_tex_2(sK2,X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f103,f27])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(X0) | v2_tex_2(sK2,X0)) )),
% 0.20/0.49    inference(resolution,[],[f99,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    v2_tex_2(sK2,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f47,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    v2_tex_2(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f46,f27])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    v2_tex_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f35,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    v3_tex_2(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK4(X0,X1) != X1 & r1_tarski(X1,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1) != X1 & r1_tarski(X1,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(rectify,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(X1) | v2_tex_2(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f43,f25])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X3,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | v2_tex_2(X3,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (v2_tex_2(X3,X1) | ~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_tex_2(X3,X1) | ~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_tex_2(X3,X1) | (~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f144,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ~v3_tex_2(sK2,sK1)),
% 0.20/0.50    inference(forward_demodulation,[],[f32,f30])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ~v3_tex_2(sK3,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    v3_tex_2(sK2,sK1) | ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(resolution,[],[f143,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK1) | ~v2_tex_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f95,f26])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK1) | ~v2_tex_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK1)) )),
% 0.20/0.50    inference(superposition,[],[f37,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.50    inference(superposition,[],[f51,f29])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = X0) )),
% 0.20/0.50    inference(resolution,[],[f49,f25])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X0) = X1 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2)) )),
% 0.20/0.50    inference(resolution,[],[f41,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f142,f26])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f141,f45])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f140,f111])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f139,f44])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK2,sK1) | ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f138,f25])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_tex_2(sK2,sK1) | ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f137,f27])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_tex_2(sK2,sK1) | ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f135,f31])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_tex_2(sK2,sK1) | ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.50    inference(resolution,[],[f134,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_tex_2(sK4(X1,X0),X2) | ~m1_subset_1(sK4(X1,X0),k1_zfmisc_1(u1_struct_0(X2))) | ~v3_tex_2(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | v3_tex_2(X0,X1) | ~v2_tex_2(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f97,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK4(X0,X1) != X1 | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (sK4(X1,X0) = X0 | ~v2_tex_2(sK4(X1,X0),X2) | ~m1_subset_1(sK4(X1,X0),k1_zfmisc_1(u1_struct_0(X2))) | ~v3_tex_2(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | v3_tex_2(X0,X1) | ~v2_tex_2(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 0.20/0.50    inference(resolution,[],[f36,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,sK4(X0,X1)) | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r1_tarski(X1,X3) | X1 = X3 | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    v2_tex_2(sK4(sK1,sK2),sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f133,f27])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    v2_tex_2(sK4(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f132,f111])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    v2_tex_2(sK4(sK1,sK2),sK0) | ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f131,f44])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    v2_tex_2(sK4(sK1,sK2),sK0) | v3_tex_2(sK2,sK1) | ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(resolution,[],[f128,f96])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK4(sK1,sK2),sK0)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v2_tex_2(sK4(sK1,sK2),sK0)),
% 0.20/0.50    inference(resolution,[],[f122,f25])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v2_tex_2(sK4(sK1,sK2),X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f121,f27])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tex_2(sK4(sK1,sK2),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f119,f44])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tex_2(sK4(sK1,sK2),X0) | v3_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.50    inference(resolution,[],[f116,f111])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~v2_tex_2(X2,sK1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(sK4(sK1,X2),X1) | v3_tex_2(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f115,f96])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(sK4(sK1,X2),X1) | v3_tex_2(X2,sK1) | ~v2_tex_2(X2,sK1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f114,f55])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ( ! [X2,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(sK4(sK1,X2),X1) | v3_tex_2(X2,sK1) | ~v2_tex_2(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f113,f26])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X2,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(sK1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(sK4(sK1,X2),X1) | v3_tex_2(X2,sK1) | ~v2_tex_2(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 0.20/0.50    inference(resolution,[],[f102,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_tex_2(sK4(X0,X1),X0) | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~v2_tex_2(X2,sK1) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | v2_tex_2(X2,X3)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f101,f55])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X2,X3] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~v2_tex_2(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(X3) | v2_tex_2(X2,X3)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f100,f29])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~v2_tex_2(X2,sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(X3) | v2_tex_2(X2,X3)) )),
% 0.20/0.50    inference(resolution,[],[f43,f26])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (27554)------------------------------
% 0.20/0.50  % (27554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27554)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (27554)Memory used [KB]: 6268
% 0.20/0.50  % (27554)Time elapsed: 0.052 s
% 0.20/0.50  % (27554)------------------------------
% 0.20/0.50  % (27554)------------------------------
% 0.20/0.50  % (27531)Success in time 0.136 s
%------------------------------------------------------------------------------
