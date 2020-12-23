%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  120 (7264 expanded)
%              Number of leaves         :   11 (2243 expanded)
%              Depth                    :   56
%              Number of atoms          :  578 (88290 expanded)
%              Number of equality atoms :  104 (8378 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(subsumption_resolution,[],[f243,f37])).

fof(f37,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
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
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f243,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
    inference(forward_demodulation,[],[f242,f80])).

fof(f80,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( sK2 != sK2
    | u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(superposition,[],[f76,f66])).

fof(f66,plain,(
    sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f36,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,
    ( sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f44,f62])).

fof(f62,plain,(
    v1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f61,f33])).

fof(f33,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,
    ( v1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f60,f34])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,
    ( v1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(superposition,[],[f47,f37])).

fof(f47,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f76,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != sK2
      | u1_struct_0(sK1) = X2 ) ),
    inference(forward_demodulation,[],[f74,f37])).

fof(f74,plain,(
    ! [X2,X3] :
      ( u1_struct_0(sK1) = X2
      | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ) ),
    inference(resolution,[],[f71,f34])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f52,f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f242,plain,(
    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f241,f105])).

fof(f105,plain,(
    u1_pre_topc(sK1) = u1_pre_topc(sK2) ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( sK2 != sK2
    | u1_pre_topc(sK1) = u1_pre_topc(sK2) ),
    inference(superposition,[],[f101,f37])).

fof(f101,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != sK2
      | u1_pre_topc(sK2) = X1 ) ),
    inference(forward_demodulation,[],[f99,f82])).

fof(f82,plain,(
    sK2 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f66,f80])).

fof(f99,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
      | u1_pre_topc(sK2) = X1 ) ),
    inference(resolution,[],[f90,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f83,f36])).

fof(f83,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f43,f80])).

fof(f241,plain,(
    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f240,f36])).

fof(f240,plain,
    ( ~ l1_pre_topc(sK2)
    | sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(resolution,[],[f239,f202])).

fof(f202,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ) ),
    inference(trivial_inequality_removal,[],[f199])).

fof(f199,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK0)
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ) ),
    inference(resolution,[],[f198,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ) ),
    inference(forward_demodulation,[],[f197,f37])).

fof(f197,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f196,f32])).

fof(f196,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f34])).

fof(f195,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f193,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f193,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f192,f37])).

fof(f192,plain,
    ( m1_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,
    ( m1_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f184,f34])).

fof(f184,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
      | m1_pre_topc(sK1,sK0) ) ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK0)
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
      | m1_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f180,f32])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
      | m1_pre_topc(sK1,sK0) ) ),
    inference(forward_demodulation,[],[f179,f37])).

fof(f179,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(forward_demodulation,[],[f178,f80])).

fof(f178,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))
      | m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(forward_demodulation,[],[f177,f105])).

fof(f177,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f176,f32])).

fof(f176,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f175,f36])).

fof(f175,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f45,f41])).

fof(f41,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f239,plain,(
    ~ m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f238,f234])).

fof(f234,plain,(
    v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f38,f233])).

fof(f233,plain,(
    ~ v1_tsep_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f232,f214])).

fof(f214,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ v1_tsep_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f213,f37])).

fof(f213,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | ~ v1_tsep_1(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f212,f80])).

fof(f212,plain,
    ( sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))
    | ~ v1_tsep_1(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f211,f105])).

fof(f211,plain,
    ( sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ v1_tsep_1(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f207,f36])).

fof(f207,plain,
    ( ~ l1_pre_topc(sK2)
    | sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ v1_tsep_1(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(resolution,[],[f202,f194])).

fof(f194,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f42,f193])).

fof(f42,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f232,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f231,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f231,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f230,f32])).

fof(f230,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f228,f193])).

fof(f228,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f220,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f55,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f220,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f219,f37])).

fof(f219,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f218,f80])).

fof(f218,plain,
    ( sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f217,f105])).

fof(f217,plain,
    ( sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f216,f31])).

fof(f216,plain,
    ( sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f215,f32])).

fof(f215,plain,
    ( sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f208,f36])).

fof(f208,plain,
    ( ~ l1_pre_topc(sK2)
    | sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f202,f89])).

fof(f89,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(sK2,X3)
      | v3_pre_topc(u1_struct_0(sK1),X3)
      | ~ v1_tsep_1(sK2,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(superposition,[],[f59,f80])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f57,f46])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,
    ( v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f238,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f237,f193])).

fof(f237,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f236,f31])).

fof(f236,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f235,f32])).

fof(f235,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(resolution,[],[f233,f132])).

fof(f132,plain,(
    ! [X0] :
      ( v1_tsep_1(sK2,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v1_tsep_1(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( v1_tsep_1(sK2,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v1_tsep_1(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f88,f59])).

fof(f88,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(u1_struct_0(sK1),X2)
      | v1_tsep_1(sK2,X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(superposition,[],[f58,f80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:19:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (5140)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (5143)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (5157)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (5151)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (5145)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (5139)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (5142)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.56  % (5143)Refutation not found, incomplete strategy% (5143)------------------------------
% 0.22/0.56  % (5143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (5138)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (5161)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.56  % (5140)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (5160)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.57  % (5159)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.57  % (5143)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (5143)Memory used [KB]: 10746
% 0.22/0.57  % (5143)Time elapsed: 0.138 s
% 0.22/0.57  % (5143)------------------------------
% 0.22/0.57  % (5143)------------------------------
% 0.22/0.57  % (5162)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.57  % (5155)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.57  % (5137)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.57  % (5147)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.57  % (5149)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.48/0.58  % (5153)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.48/0.58  % (5156)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.48/0.58  % (5152)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.48/0.58  % (5154)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.48/0.58  % (5141)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.48/0.58  % SZS output start Proof for theBenchmark
% 1.48/0.58  fof(f244,plain,(
% 1.48/0.58    $false),
% 1.48/0.58    inference(subsumption_resolution,[],[f243,f37])).
% 1.48/0.58  fof(f37,plain,(
% 1.48/0.58    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f28,plain,(
% 1.48/0.58    (((~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_tsep_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 1.48/0.58  fof(f25,plain,(
% 1.48/0.58    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f26,plain,(
% 1.48/0.58    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f27,plain,(
% 1.48/0.58    ? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_tsep_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f24,plain,(
% 1.48/0.58    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.48/0.58    inference(flattening,[],[f23])).
% 1.48/0.58  fof(f23,plain,(
% 1.48/0.58    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.48/0.58    inference(nnf_transformation,[],[f11])).
% 1.48/0.58  fof(f11,plain,(
% 1.48/0.58    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.48/0.58    inference(flattening,[],[f10])).
% 1.48/0.58  fof(f10,plain,(
% 1.48/0.58    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.48/0.58    inference(ennf_transformation,[],[f9])).
% 1.48/0.58  fof(f9,negated_conjecture,(
% 1.48/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 1.48/0.58    inference(negated_conjecture,[],[f8])).
% 1.48/0.58  fof(f8,conjecture,(
% 1.48/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).
% 1.48/0.58  fof(f243,plain,(
% 1.48/0.58    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2),
% 1.48/0.58    inference(forward_demodulation,[],[f242,f80])).
% 1.48/0.58  fof(f80,plain,(
% 1.48/0.58    u1_struct_0(sK1) = u1_struct_0(sK2)),
% 1.48/0.58    inference(trivial_inequality_removal,[],[f79])).
% 1.48/0.58  fof(f79,plain,(
% 1.48/0.58    sK2 != sK2 | u1_struct_0(sK1) = u1_struct_0(sK2)),
% 1.48/0.58    inference(superposition,[],[f76,f66])).
% 1.48/0.58  fof(f66,plain,(
% 1.48/0.58    sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.48/0.58    inference(subsumption_resolution,[],[f65,f36])).
% 1.48/0.58  fof(f36,plain,(
% 1.48/0.58    l1_pre_topc(sK2)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f65,plain,(
% 1.48/0.58    sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~l1_pre_topc(sK2)),
% 1.48/0.58    inference(resolution,[],[f44,f62])).
% 1.48/0.58  fof(f62,plain,(
% 1.48/0.58    v1_pre_topc(sK2)),
% 1.48/0.58    inference(subsumption_resolution,[],[f61,f33])).
% 1.48/0.58  fof(f33,plain,(
% 1.48/0.58    v2_pre_topc(sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f61,plain,(
% 1.48/0.58    v1_pre_topc(sK2) | ~v2_pre_topc(sK1)),
% 1.48/0.58    inference(subsumption_resolution,[],[f60,f34])).
% 1.48/0.58  fof(f34,plain,(
% 1.48/0.58    l1_pre_topc(sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f60,plain,(
% 1.48/0.58    v1_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.48/0.58    inference(superposition,[],[f47,f37])).
% 1.48/0.58  fof(f47,plain,(
% 1.48/0.58    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f19])).
% 1.48/0.58  fof(f19,plain,(
% 1.48/0.58    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.58    inference(flattening,[],[f18])).
% 1.48/0.58  fof(f18,plain,(
% 1.48/0.58    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.48/0.58    inference(ennf_transformation,[],[f3])).
% 1.48/0.58  fof(f3,axiom,(
% 1.48/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 1.48/0.58  fof(f44,plain,(
% 1.48/0.58    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f14])).
% 1.48/0.58  fof(f14,plain,(
% 1.48/0.58    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.48/0.58    inference(flattening,[],[f13])).
% 1.48/0.58  fof(f13,plain,(
% 1.48/0.58    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f1])).
% 1.48/0.58  fof(f1,axiom,(
% 1.48/0.58    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.48/0.58  fof(f76,plain,(
% 1.48/0.58    ( ! [X2,X3] : (g1_pre_topc(X2,X3) != sK2 | u1_struct_0(sK1) = X2) )),
% 1.48/0.58    inference(forward_demodulation,[],[f74,f37])).
% 1.48/0.58  fof(f74,plain,(
% 1.48/0.58    ( ! [X2,X3] : (u1_struct_0(sK1) = X2 | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )),
% 1.48/0.58    inference(resolution,[],[f71,f34])).
% 1.48/0.58  fof(f71,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X0) = X1 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2)) )),
% 1.48/0.58    inference(resolution,[],[f52,f43])).
% 1.48/0.58  fof(f43,plain,(
% 1.48/0.58    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f12])).
% 1.48/0.58  fof(f12,plain,(
% 1.48/0.58    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f2])).
% 1.48/0.58  fof(f2,axiom,(
% 1.48/0.58    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.48/0.58  fof(f52,plain,(
% 1.48/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 1.48/0.58    inference(cnf_transformation,[],[f22])).
% 1.48/0.58  fof(f22,plain,(
% 1.48/0.58    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.48/0.58    inference(ennf_transformation,[],[f4])).
% 1.48/0.58  fof(f4,axiom,(
% 1.48/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.48/0.58  fof(f242,plain,(
% 1.48/0.58    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))),
% 1.48/0.58    inference(forward_demodulation,[],[f241,f105])).
% 1.48/0.58  fof(f105,plain,(
% 1.48/0.58    u1_pre_topc(sK1) = u1_pre_topc(sK2)),
% 1.48/0.58    inference(trivial_inequality_removal,[],[f103])).
% 1.48/0.58  fof(f103,plain,(
% 1.48/0.58    sK2 != sK2 | u1_pre_topc(sK1) = u1_pre_topc(sK2)),
% 1.48/0.58    inference(superposition,[],[f101,f37])).
% 1.48/0.58  fof(f101,plain,(
% 1.48/0.58    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK2 | u1_pre_topc(sK2) = X1) )),
% 1.48/0.58    inference(forward_demodulation,[],[f99,f82])).
% 1.48/0.58  fof(f82,plain,(
% 1.48/0.58    sK2 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),
% 1.48/0.58    inference(backward_demodulation,[],[f66,f80])).
% 1.48/0.58  fof(f99,plain,(
% 1.48/0.58    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) | u1_pre_topc(sK2) = X1) )),
% 1.48/0.58    inference(resolution,[],[f90,f53])).
% 1.48/0.58  fof(f53,plain,(
% 1.48/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 1.48/0.58    inference(cnf_transformation,[],[f22])).
% 1.48/0.58  fof(f90,plain,(
% 1.48/0.58    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.48/0.58    inference(subsumption_resolution,[],[f83,f36])).
% 1.48/0.58  fof(f83,plain,(
% 1.48/0.58    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK2)),
% 1.48/0.58    inference(superposition,[],[f43,f80])).
% 1.48/0.58  fof(f241,plain,(
% 1.48/0.58    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.48/0.58    inference(subsumption_resolution,[],[f240,f36])).
% 1.48/0.58  fof(f240,plain,(
% 1.48/0.58    ~l1_pre_topc(sK2) | sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.48/0.58    inference(resolution,[],[f239,f202])).
% 1.48/0.58  fof(f202,plain,(
% 1.48/0.58    ( ! [X0] : (m1_pre_topc(X0,sK0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2) )),
% 1.48/0.58    inference(trivial_inequality_removal,[],[f199])).
% 1.48/0.58  fof(f199,plain,(
% 1.48/0.58    ( ! [X0] : (m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2) )),
% 1.48/0.58    inference(resolution,[],[f198,f32])).
% 1.48/0.58  fof(f32,plain,(
% 1.48/0.58    l1_pre_topc(sK0)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f198,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~l1_pre_topc(X1) | m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2) )),
% 1.48/0.58    inference(forward_demodulation,[],[f197,f37])).
% 1.48/0.58  fof(f197,plain,(
% 1.48/0.58    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 1.48/0.58    inference(subsumption_resolution,[],[f196,f32])).
% 1.48/0.58  fof(f196,plain,(
% 1.48/0.58    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0)) )),
% 1.48/0.58    inference(subsumption_resolution,[],[f195,f34])).
% 1.48/0.58  fof(f195,plain,(
% 1.48/0.58    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0)) )),
% 1.48/0.58    inference(resolution,[],[f193,f45])).
% 1.48/0.58  fof(f45,plain,(
% 1.48/0.58    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f16])).
% 1.48/0.58  fof(f16,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.48/0.58    inference(flattening,[],[f15])).
% 1.48/0.58  fof(f15,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f5])).
% 1.48/0.59  fof(f5,axiom,(
% 1.48/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).
% 1.48/0.59  fof(f193,plain,(
% 1.48/0.59    m1_pre_topc(sK1,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f192,f37])).
% 1.48/0.59  fof(f192,plain,(
% 1.48/0.59    m1_pre_topc(sK1,sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2),
% 1.48/0.59    inference(duplicate_literal_removal,[],[f190])).
% 1.48/0.59  fof(f190,plain,(
% 1.48/0.59    m1_pre_topc(sK1,sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 | m1_pre_topc(sK1,sK0)),
% 1.48/0.59    inference(resolution,[],[f184,f34])).
% 1.48/0.59  fof(f184,plain,(
% 1.48/0.59    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 | m1_pre_topc(sK1,sK0)) )),
% 1.48/0.59    inference(trivial_inequality_removal,[],[f181])).
% 1.48/0.59  fof(f181,plain,(
% 1.48/0.59    ( ! [X0] : (m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 | m1_pre_topc(sK1,sK0)) )),
% 1.48/0.59    inference(resolution,[],[f180,f32])).
% 1.48/0.59  fof(f180,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~l1_pre_topc(X1) | m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 | m1_pre_topc(sK1,sK0)) )),
% 1.48/0.59    inference(forward_demodulation,[],[f179,f37])).
% 1.48/0.59  fof(f179,plain,(
% 1.48/0.59    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,sK0)) )),
% 1.48/0.59    inference(forward_demodulation,[],[f178,f80])).
% 1.48/0.59  fof(f178,plain,(
% 1.48/0.59    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1)) | m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,sK0)) )),
% 1.48/0.59    inference(forward_demodulation,[],[f177,f105])).
% 1.48/0.59  fof(f177,plain,(
% 1.48/0.59    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,sK0)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f176,f32])).
% 1.48/0.59  fof(f176,plain,(
% 1.48/0.59    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f175,f36])).
% 1.48/0.59  fof(f175,plain,(
% 1.48/0.59    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0)) )),
% 1.48/0.59    inference(resolution,[],[f45,f41])).
% 1.48/0.59  fof(f41,plain,(
% 1.48/0.59    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f28])).
% 1.48/0.59  fof(f239,plain,(
% 1.48/0.59    ~m1_pre_topc(sK2,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f238,f234])).
% 1.48/0.59  fof(f234,plain,(
% 1.48/0.59    v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f38,f233])).
% 1.48/0.59  fof(f233,plain,(
% 1.48/0.59    ~v1_tsep_1(sK2,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f232,f214])).
% 1.48/0.59  fof(f214,plain,(
% 1.48/0.59    ~v1_tsep_1(sK1,sK0) | ~v1_tsep_1(sK2,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f213,f37])).
% 1.48/0.59  fof(f213,plain,(
% 1.48/0.59    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 | ~v1_tsep_1(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(forward_demodulation,[],[f212,f80])).
% 1.48/0.59  fof(f212,plain,(
% 1.48/0.59    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1)) | ~v1_tsep_1(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(forward_demodulation,[],[f211,f105])).
% 1.48/0.59  fof(f211,plain,(
% 1.48/0.59    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~v1_tsep_1(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f207,f36])).
% 1.48/0.59  fof(f207,plain,(
% 1.48/0.59    ~l1_pre_topc(sK2) | sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~v1_tsep_1(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(resolution,[],[f202,f194])).
% 1.48/0.59  fof(f194,plain,(
% 1.48/0.59    ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f42,f193])).
% 1.48/0.59  fof(f42,plain,(
% 1.48/0.59    ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f28])).
% 1.48/0.59  fof(f232,plain,(
% 1.48/0.59    ~v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f231,f31])).
% 1.48/0.59  fof(f31,plain,(
% 1.48/0.59    v2_pre_topc(sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f28])).
% 1.48/0.59  fof(f231,plain,(
% 1.48/0.59    ~v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0) | ~v2_pre_topc(sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f230,f32])).
% 1.48/0.59  fof(f230,plain,(
% 1.48/0.59    ~v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f228,f193])).
% 1.48/0.59  fof(f228,plain,(
% 1.48/0.59    ~v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.48/0.59    inference(resolution,[],[f220,f58])).
% 1.48/0.59  fof(f58,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f55,f46])).
% 1.48/0.59  fof(f46,plain,(
% 1.48/0.59    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f17])).
% 1.48/0.59  fof(f17,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f7])).
% 1.48/0.59  fof(f7,axiom,(
% 1.48/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.48/0.59  fof(f55,plain,(
% 1.48/0.59    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.59    inference(equality_resolution,[],[f50])).
% 1.48/0.59  fof(f50,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f30])).
% 1.48/0.59  fof(f30,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.59    inference(flattening,[],[f29])).
% 1.48/0.59  fof(f29,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.59    inference(nnf_transformation,[],[f21])).
% 1.48/0.59  fof(f21,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.59    inference(flattening,[],[f20])).
% 1.48/0.59  fof(f20,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.48/0.59    inference(ennf_transformation,[],[f6])).
% 1.48/0.59  fof(f6,axiom,(
% 1.48/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.48/0.59  fof(f220,plain,(
% 1.48/0.59    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK2,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f219,f37])).
% 1.48/0.59  fof(f219,plain,(
% 1.48/0.59    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK2,sK0)),
% 1.48/0.59    inference(forward_demodulation,[],[f218,f80])).
% 1.48/0.59  fof(f218,plain,(
% 1.48/0.59    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK2,sK0)),
% 1.48/0.59    inference(forward_demodulation,[],[f217,f105])).
% 1.48/0.59  fof(f217,plain,(
% 1.48/0.59    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK2,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f216,f31])).
% 1.48/0.59  fof(f216,plain,(
% 1.48/0.59    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK2,sK0) | ~v2_pre_topc(sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f215,f32])).
% 1.48/0.59  fof(f215,plain,(
% 1.48/0.59    sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f208,f36])).
% 1.48/0.59  fof(f208,plain,(
% 1.48/0.59    ~l1_pre_topc(sK2) | sK2 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.48/0.59    inference(resolution,[],[f202,f89])).
% 1.48/0.59  fof(f89,plain,(
% 1.48/0.59    ( ! [X3] : (~m1_pre_topc(sK2,X3) | v3_pre_topc(u1_struct_0(sK1),X3) | ~v1_tsep_1(sK2,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) )),
% 1.48/0.59    inference(superposition,[],[f59,f80])).
% 1.48/0.59  fof(f59,plain,(
% 1.48/0.59    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f57,f46])).
% 1.48/0.59  fof(f57,plain,(
% 1.48/0.59    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.59    inference(duplicate_literal_removal,[],[f56])).
% 1.48/0.59  fof(f56,plain,(
% 1.48/0.59    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.59    inference(equality_resolution,[],[f49])).
% 1.48/0.59  fof(f49,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f30])).
% 1.48/0.59  fof(f38,plain,(
% 1.48/0.59    v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f28])).
% 1.48/0.59  fof(f238,plain,(
% 1.48/0.59    ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f237,f193])).
% 1.48/0.59  fof(f237,plain,(
% 1.48/0.59    ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f236,f31])).
% 1.48/0.59  fof(f236,plain,(
% 1.48/0.59    ~m1_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f235,f32])).
% 1.48/0.59  fof(f235,plain,(
% 1.48/0.59    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.48/0.59    inference(resolution,[],[f233,f132])).
% 1.48/0.59  fof(f132,plain,(
% 1.48/0.59    ( ! [X0] : (v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~v1_tsep_1(sK1,X0)) )),
% 1.48/0.59    inference(duplicate_literal_removal,[],[f131])).
% 1.48/0.59  fof(f131,plain,(
% 1.48/0.59    ( ! [X0] : (v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~v1_tsep_1(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.59    inference(resolution,[],[f88,f59])).
% 1.48/0.59  fof(f88,plain,(
% 1.48/0.59    ( ! [X2] : (~v3_pre_topc(u1_struct_0(sK1),X2) | v1_tsep_1(sK2,X2) | ~m1_pre_topc(sK2,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) )),
% 1.48/0.59    inference(superposition,[],[f58,f80])).
% 1.48/0.59  % SZS output end Proof for theBenchmark
% 1.48/0.59  % (5140)------------------------------
% 1.48/0.59  % (5140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.59  % (5140)Termination reason: Refutation
% 1.48/0.59  
% 1.48/0.59  % (5140)Memory used [KB]: 6268
% 1.48/0.59  % (5140)Time elapsed: 0.138 s
% 1.48/0.59  % (5140)------------------------------
% 1.48/0.59  % (5140)------------------------------
% 1.48/0.59  % (5144)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.48/0.59  % (5136)Success in time 0.214 s
%------------------------------------------------------------------------------
