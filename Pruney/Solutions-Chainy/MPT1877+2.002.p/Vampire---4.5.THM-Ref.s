%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  126 (4088 expanded)
%              Number of leaves         :   16 (1619 expanded)
%              Depth                    :   31
%              Number of atoms          :  454 (29570 expanded)
%              Number of equality atoms :   74 (7513 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f456,plain,(
    $false ),
    inference(subsumption_resolution,[],[f455,f326])).

fof(f326,plain,(
    m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f321,f209])).

fof(f209,plain,(
    u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f206,f104])).

fof(f104,plain,(
    m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f103,f40])).

fof(f40,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v3_tex_2(sK6,sK4)
    & v3_tex_2(sK5,sK3)
    & sK5 = sK6
    & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK4)
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f11,f27,f26,f25,f24])).

fof(f24,plain,
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
                  & v3_tex_2(X2,sK3)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_tex_2(X3,X1)
                & v3_tex_2(X2,sK3)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_tex_2(X3,sK4)
              & v3_tex_2(X2,sK3)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_tex_2(X3,sK4)
            & v3_tex_2(X2,sK3)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X3] :
          ( ~ v3_tex_2(X3,sK4)
          & v3_tex_2(sK5,sK3)
          & sK5 = X3
          & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ~ v3_tex_2(X3,sK4)
        & v3_tex_2(sK5,sK3)
        & sK5 = X3
        & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ~ v3_tex_2(sK6,sK4)
      & v3_tex_2(sK5,sK3)
      & sK5 = sK6
      & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f103,plain,
    ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f71,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f206,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(resolution,[],[f205,f139])).

fof(f139,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK4)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ) ),
    inference(subsumption_resolution,[],[f134,f41])).

fof(f41,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | m1_pre_topc(X0,sK4)
      | ~ l1_pre_topc(sK4) ) ),
    inference(superposition,[],[f64,f44])).

fof(f44,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f205,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f204,f41])).

fof(f204,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f178,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f178,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(resolution,[],[f172,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f172,plain,(
    r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(resolution,[],[f168,f76])).

fof(f76,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | r1_tarski(u1_struct_0(X4),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f40,f52])).

fof(f168,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(subsumption_resolution,[],[f164,f40])).

fof(f164,plain,
    ( m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f163,f64])).

fof(f163,plain,(
    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(forward_demodulation,[],[f108,f44])).

fof(f108,plain,(
    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f107,f41])).

fof(f107,plain,
    ( m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f81,f49])).

fof(f81,plain,(
    m1_pre_topc(sK4,sK4) ),
    inference(resolution,[],[f41,f48])).

fof(f321,plain,(
    m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(resolution,[],[f316,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK7(X0,X1) != X0
          & r1_tarski(X0,sK7(X0,X1))
          & v2_tex_2(sK7(X0,X1),X1)
          & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK7(X0,X1) != X0
        & r1_tarski(X0,sK7(X0,X1))
        & v2_tex_2(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f316,plain,(
    ~ sP0(sK5,sK4) ),
    inference(subsumption_resolution,[],[f312,f133])).

fof(f133,plain,(
    ~ sP1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f132,f92])).

fof(f92,plain,(
    ~ v3_tex_2(sK5,sK4) ),
    inference(forward_demodulation,[],[f47,f45])).

fof(f45,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ~ v3_tex_2(sK6,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f132,plain,
    ( v3_tex_2(sK5,sK4)
    | ~ sP1(sK4,sK5) ),
    inference(resolution,[],[f128,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X0,X1)
      | ~ sP1(X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f128,plain,(
    sP2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f124,f41])).

fof(f124,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f115,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f22,f21,f20])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f115,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_demodulation,[],[f43,f45])).

fof(f43,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f28])).

fof(f312,plain,
    ( sP1(sK4,sK5)
    | ~ sP0(sK5,sK4) ),
    inference(resolution,[],[f309,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f309,plain,(
    v2_tex_2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f308,f42])).

fof(f42,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f28])).

fof(f308,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(sK5,sK4) ),
    inference(forward_demodulation,[],[f307,f209])).

fof(f307,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_tex_2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f306,f217])).

fof(f217,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4)) ),
    inference(backward_demodulation,[],[f44,f209])).

fof(f306,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_tex_2(sK5,sK4) ),
    inference(forward_demodulation,[],[f304,f209])).

fof(f304,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_tex_2(sK5,sK4) ),
    inference(resolution,[],[f300,f41])).

fof(f300,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(sK5,X1) ) ),
    inference(subsumption_resolution,[],[f99,f112])).

fof(f112,plain,(
    v2_tex_2(sK5,sK3) ),
    inference(resolution,[],[f111,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    sP1(sK3,sK5) ),
    inference(subsumption_resolution,[],[f109,f46])).

fof(f46,plain,(
    v3_tex_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f109,plain,
    ( sP1(sK3,sK5)
    | ~ v3_tex_2(sK5,sK3) ),
    inference(resolution,[],[f98,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v3_tex_2(X0,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    sP2(sK5,sK3) ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f94,plain,
    ( sP2(sK5,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f42,f63])).

fof(f99,plain,(
    ! [X1] :
      ( v2_tex_2(sK5,X1)
      | ~ v2_tex_2(sK5,sK3)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f96,f40])).

fof(f96,plain,(
    ! [X1] :
      ( v2_tex_2(sK5,X1)
      | ~ v2_tex_2(sK5,sK3)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f42,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X3,X1)
      | ~ v2_tex_2(X3,X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_tex_2(X3,X1)
      | ~ v2_tex_2(X2,X0)
      | X2 != X3
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f455,plain,(
    ~ m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f452,f322])).

fof(f322,plain,(
    v2_tex_2(sK7(sK5,sK4),sK4) ),
    inference(resolution,[],[f316,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v2_tex_2(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f452,plain,
    ( ~ v2_tex_2(sK7(sK5,sK4),sK4)
    | ~ m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f449,f387])).

fof(f387,plain,(
    ! [X1] :
      ( v2_tex_2(X1,sK3)
      | ~ v2_tex_2(X1,sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(duplicate_literal_removal,[],[f386])).

% (13426)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (13402)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (13415)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (13408)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (13417)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (13405)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f386,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v2_tex_2(X1,sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | v2_tex_2(X1,sK3) ) ),
    inference(forward_demodulation,[],[f385,f209])).

fof(f385,plain,(
    ! [X1] :
      ( ~ v2_tex_2(X1,sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
      | v2_tex_2(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f384,f217])).

fof(f384,plain,(
    ! [X1] :
      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4))
      | ~ v2_tex_2(X1,sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
      | v2_tex_2(X1,sK3) ) ),
    inference(forward_demodulation,[],[f382,f209])).

fof(f382,plain,(
    ! [X1] :
      ( ~ v2_tex_2(X1,sK4)
      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
      | v2_tex_2(X1,sK3) ) ),
    inference(resolution,[],[f80,f41])).

fof(f80,plain,(
    ! [X10,X9] :
      ( ~ l1_pre_topc(X10)
      | ~ v2_tex_2(X9,X10)
      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X10)))
      | v2_tex_2(X9,sK3) ) ),
    inference(resolution,[],[f40,f68])).

fof(f449,plain,(
    ~ v2_tex_2(sK7(sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f448,f326])).

fof(f448,plain,
    ( ~ v2_tex_2(sK7(sK5,sK4),sK3)
    | ~ m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f444,f324])).

fof(f324,plain,(
    sK5 != sK7(sK5,sK4) ),
    inference(resolution,[],[f316,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | sK7(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f444,plain,
    ( sK5 = sK7(sK5,sK4)
    | ~ v2_tex_2(sK7(sK5,sK4),sK3)
    | ~ m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f122,f323])).

fof(f323,plain,(
    r1_tarski(sK5,sK7(sK5,sK4)) ),
    inference(resolution,[],[f316,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(X0,sK7(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK5,X0)
      | sK5 = X0
      | ~ v2_tex_2(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f113,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r1_tarski(X0,X3)
      | ~ v2_tex_2(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f113,plain,(
    sP0(sK5,sK3) ),
    inference(resolution,[],[f111,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:48:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (13411)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.46  % (13419)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.49  % (13407)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (13406)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (13404)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (13416)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (13423)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (13424)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (13414)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (13420)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (13422)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (13418)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (13403)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13413)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (13410)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (13427)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (13409)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (13421)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (13410)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f456,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f455,f326])).
% 0.21/0.52  fof(f326,plain,(
% 0.21/0.52    m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(forward_demodulation,[],[f321,f209])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    u1_struct_0(sK3) = u1_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f206,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    l1_pre_topc(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    (((~v3_tex_2(sK6,sK4) & v3_tex_2(sK5,sK3) & sK5 = sK6 & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK4)) & l1_pre_topc(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f11,f27,f26,f25,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,sK3) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(X1)) & l1_pre_topc(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,sK3) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v3_tex_2(X3,sK4) & v3_tex_2(X2,sK3) & X2 = X3 & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (~v3_tex_2(X3,sK4) & v3_tex_2(X2,sK3) & X2 = X3 & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) => (? [X3] : (~v3_tex_2(X3,sK4) & v3_tex_2(sK5,sK3) & sK5 = X3 & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ? [X3] : (~v3_tex_2(X3,sK4) & v3_tex_2(sK5,sK3) & sK5 = X3 & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) => (~v3_tex_2(sK6,sK4) & v3_tex_2(sK5,sK3) & sK5 = sK6 & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v3_tex_2(X3,X1) & (v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tex_2)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(sK3)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK3)),
% 0.21/0.52    inference(resolution,[],[f71,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK3)),
% 0.21/0.52    inference(resolution,[],[f40,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    u1_struct_0(sK3) = u1_struct_0(sK4) | ~m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 0.21/0.52    inference(resolution,[],[f205,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X0] : (m1_pre_topc(X0,sK4) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f134,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    l1_pre_topc(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | m1_pre_topc(X0,sK4) | ~l1_pre_topc(sK4)) )),
% 0.21/0.52    inference(superposition,[],[f64,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    ~m1_pre_topc(sK3,sK4) | u1_struct_0(sK3) = u1_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f204,f41])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    u1_struct_0(sK3) = u1_struct_0(sK4) | ~m1_pre_topc(sK3,sK4) | ~l1_pre_topc(sK4)),
% 0.21/0.52    inference(resolution,[],[f178,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    ~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) | u1_struct_0(sK3) = u1_struct_0(sK4)),
% 0.21/0.52    inference(resolution,[],[f172,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3))),
% 0.21/0.52    inference(resolution,[],[f168,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | r1_tarski(u1_struct_0(X4),u1_struct_0(sK3))) )),
% 0.21/0.52    inference(resolution,[],[f40,f52])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    m1_pre_topc(sK4,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f164,f40])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    m1_pre_topc(sK4,sK3) | ~l1_pre_topc(sK3)),
% 0.21/0.52    inference(resolution,[],[f163,f64])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 0.21/0.52    inference(forward_demodulation,[],[f108,f44])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f41])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~l1_pre_topc(sK4)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK4)),
% 0.21/0.52    inference(resolution,[],[f81,f49])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    m1_pre_topc(sK4,sK4)),
% 0.21/0.52    inference(resolution,[],[f41,f48])).
% 0.21/0.52  fof(f321,plain,(
% 0.21/0.52    m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.52    inference(resolution,[],[f316,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | (sK7(X0,X1) != X0 & r1_tarski(X0,sK7(X0,X1)) & v2_tex_2(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK7(X0,X1) != X0 & r1_tarski(X0,sK7(X0,X1)) & v2_tex_2(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    ~sP0(sK5,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f312,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~sP1(sK4,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f132,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~v3_tex_2(sK5,sK4)),
% 0.21/0.52    inference(forward_demodulation,[],[f47,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    sK5 = sK6),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~v3_tex_2(sK6,sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    v3_tex_2(sK5,sK4) | ~sP1(sK4,sK5)),
% 0.21/0.52    inference(resolution,[],[f128,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v3_tex_2(X0,X1) | ~sP1(X1,X0) | ~sP2(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.21/0.52    inference(rectify,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    sP2(sK5,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f124,f41])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    sP2(sK5,sK4) | ~l1_pre_topc(sK4)),
% 0.21/0.52    inference(resolution,[],[f115,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(definition_folding,[],[f18,f22,f21,f20])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.52    inference(forward_demodulation,[],[f43,f45])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    sP1(sK4,sK5) | ~sP0(sK5,sK4)),
% 0.21/0.52    inference(resolution,[],[f309,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    v2_tex_2(sK5,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f308,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | v2_tex_2(sK5,sK4)),
% 0.21/0.52    inference(forward_demodulation,[],[f307,f209])).
% 0.21/0.52  fof(f307,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | v2_tex_2(sK5,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f306,f217])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4))),
% 0.21/0.52    inference(backward_demodulation,[],[f44,f209])).
% 0.21/0.52  fof(f306,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | v2_tex_2(sK5,sK4)),
% 0.21/0.52    inference(forward_demodulation,[],[f304,f209])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | v2_tex_2(sK5,sK4)),
% 0.21/0.52    inference(resolution,[],[f300,f41])).
% 0.21/0.52  fof(f300,plain,(
% 0.21/0.52    ( ! [X1] : (~l1_pre_topc(X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(sK5,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    v2_tex_2(sK5,sK3)),
% 0.21/0.52    inference(resolution,[],[f111,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~sP1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    sP1(sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f109,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    v3_tex_2(sK5,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    sP1(sK3,sK5) | ~v3_tex_2(sK5,sK3)),
% 0.21/0.52    inference(resolution,[],[f98,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP1(X1,X0) | ~v3_tex_2(X0,X1) | ~sP2(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    sP2(sK5,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f94,f40])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    sP2(sK5,sK3) | ~l1_pre_topc(sK3)),
% 0.21/0.52    inference(resolution,[],[f42,f63])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X1] : (v2_tex_2(sK5,X1) | ~v2_tex_2(sK5,sK3) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f96,f40])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X1] : (v2_tex_2(sK5,X1) | ~v2_tex_2(sK5,sK3) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK3)) )),
% 0.21/0.52    inference(resolution,[],[f42,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (v2_tex_2(X3,X1) | ~v2_tex_2(X3,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v2_tex_2(X3,X1) | ~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_tex_2(X3,X1) | ~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_tex_2(X3,X1) | (~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).
% 0.21/0.52  fof(f455,plain,(
% 0.21/0.52    ~m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f452,f322])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    v2_tex_2(sK7(sK5,sK4),sK4)),
% 0.21/0.52    inference(resolution,[],[f316,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X0,X1) | v2_tex_2(sK7(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f452,plain,(
% 0.21/0.52    ~v2_tex_2(sK7(sK5,sK4),sK4) | ~m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(resolution,[],[f449,f387])).
% 0.21/0.52  fof(f387,plain,(
% 0.21/0.52    ( ! [X1] : (v2_tex_2(X1,sK3) | ~v2_tex_2(X1,sK4) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f386])).
% 0.21/0.52  % (13426)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (13402)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (13415)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (13408)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.38/0.53  % (13417)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.38/0.53  % (13405)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.38/0.53  fof(f386,plain,(
% 1.38/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_tex_2(X1,sK4) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | v2_tex_2(X1,sK3)) )),
% 1.38/0.53    inference(forward_demodulation,[],[f385,f209])).
% 1.38/0.53  fof(f385,plain,(
% 1.38/0.53    ( ! [X1] : (~v2_tex_2(X1,sK4) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) | v2_tex_2(X1,sK3)) )),
% 1.38/0.53    inference(subsumption_resolution,[],[f384,f217])).
% 1.38/0.53  fof(f384,plain,(
% 1.38/0.53    ( ! [X1] : (g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~v2_tex_2(X1,sK4) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) | v2_tex_2(X1,sK3)) )),
% 1.38/0.53    inference(forward_demodulation,[],[f382,f209])).
% 1.38/0.53  fof(f382,plain,(
% 1.38/0.53    ( ! [X1] : (~v2_tex_2(X1,sK4) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) | v2_tex_2(X1,sK3)) )),
% 1.38/0.53    inference(resolution,[],[f80,f41])).
% 1.38/0.53  fof(f80,plain,(
% 1.38/0.53    ( ! [X10,X9] : (~l1_pre_topc(X10) | ~v2_tex_2(X9,X10) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X10))) | v2_tex_2(X9,sK3)) )),
% 1.38/0.53    inference(resolution,[],[f40,f68])).
% 1.38/0.53  fof(f449,plain,(
% 1.38/0.53    ~v2_tex_2(sK7(sK5,sK4),sK3)),
% 1.38/0.53    inference(subsumption_resolution,[],[f448,f326])).
% 1.38/0.53  fof(f448,plain,(
% 1.38/0.53    ~v2_tex_2(sK7(sK5,sK4),sK3) | ~m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.38/0.53    inference(subsumption_resolution,[],[f444,f324])).
% 1.38/0.53  fof(f324,plain,(
% 1.38/0.53    sK5 != sK7(sK5,sK4)),
% 1.38/0.53    inference(resolution,[],[f316,f62])).
% 1.38/0.53  fof(f62,plain,(
% 1.38/0.53    ( ! [X0,X1] : (sP0(X0,X1) | sK7(X0,X1) != X0) )),
% 1.38/0.53    inference(cnf_transformation,[],[f37])).
% 1.38/0.53  fof(f444,plain,(
% 1.38/0.53    sK5 = sK7(sK5,sK4) | ~v2_tex_2(sK7(sK5,sK4),sK3) | ~m1_subset_1(sK7(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.38/0.53    inference(resolution,[],[f122,f323])).
% 1.38/0.53  fof(f323,plain,(
% 1.38/0.53    r1_tarski(sK5,sK7(sK5,sK4))),
% 1.38/0.53    inference(resolution,[],[f316,f61])).
% 1.38/0.53  fof(f61,plain,(
% 1.38/0.53    ( ! [X0,X1] : (sP0(X0,X1) | r1_tarski(X0,sK7(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f37])).
% 1.38/0.53  fof(f122,plain,(
% 1.38/0.53    ( ! [X0] : (~r1_tarski(sK5,X0) | sK5 = X0 | ~v2_tex_2(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 1.38/0.53    inference(resolution,[],[f113,f58])).
% 1.38/0.53  fof(f58,plain,(
% 1.38/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f37])).
% 1.38/0.53  fof(f113,plain,(
% 1.38/0.53    sP0(sK5,sK3)),
% 1.38/0.53    inference(resolution,[],[f111,f56])).
% 1.38/0.53  fof(f56,plain,(
% 1.38/0.53    ( ! [X0,X1] : (sP0(X1,X0) | ~sP1(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f33])).
% 1.38/0.53  % SZS output end Proof for theBenchmark
% 1.38/0.53  % (13410)------------------------------
% 1.38/0.53  % (13410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (13410)Termination reason: Refutation
% 1.38/0.53  
% 1.38/0.53  % (13410)Memory used [KB]: 1791
% 1.38/0.53  % (13410)Time elapsed: 0.114 s
% 1.38/0.53  % (13410)------------------------------
% 1.38/0.53  % (13410)------------------------------
% 1.38/0.54  % (13401)Success in time 0.177 s
%------------------------------------------------------------------------------
