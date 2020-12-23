%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1851+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   33 (  94 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 431 expanded)
%              Number of equality atoms :   32 ( 106 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4289,plain,(
    $false ),
    inference(global_subsumption,[],[f3756,f3753,f4288])).

fof(f4288,plain,
    ( v2_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(trivial_inequality_removal,[],[f4287])).

fof(f4287,plain,
    ( u1_pre_topc(sK6) != u1_pre_topc(sK6)
    | v2_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(forward_demodulation,[],[f4286,f4256])).

fof(f4256,plain,(
    u1_pre_topc(sK6) = u1_pre_topc(sK7) ),
    inference(unit_resulting_resolution,[],[f3754,f3946,f3802])).

fof(f3802,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3632])).

fof(f3632,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1808])).

fof(f1808,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f3946,plain,(
    m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(unit_resulting_resolution,[],[f3752,f3903])).

fof(f3903,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3681])).

fof(f3681,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3752,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f3693])).

fof(f3693,plain,
    ( ~ v2_tdlat_3(sK7)
    & v2_tdlat_3(sK6)
    & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
    & l1_pre_topc(sK7)
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f3620,f3692,f3691])).

fof(f3691,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tdlat_3(X1)
            & v2_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(sK6)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f3692,plain,
    ( ? [X1] :
        ( ~ v2_tdlat_3(X1)
        & v2_tdlat_3(sK6)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
        & l1_pre_topc(X1) )
   => ( ~ v2_tdlat_3(sK7)
      & v2_tdlat_3(sK6)
      & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
      & l1_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f3620,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3619])).

fof(f3619,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3609])).

fof(f3609,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3608])).

fof(f3608,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tex_2)).

fof(f3754,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) ),
    inference(cnf_transformation,[],[f3693])).

fof(f4286,plain,
    ( u1_pre_topc(sK6) != u1_pre_topc(sK7)
    | v2_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(forward_demodulation,[],[f4258,f3982])).

fof(f3982,plain,(
    u1_pre_topc(sK6) = k2_tarski(k1_xboole_0,u1_struct_0(sK6)) ),
    inference(unit_resulting_resolution,[],[f3752,f3755,f3786])).

fof(f3786,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3704])).

fof(f3704,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3621])).

fof(f3621,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3572])).

fof(f3572,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tdlat_3)).

fof(f3755,plain,(
    v2_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f3693])).

fof(f4258,plain,
    ( u1_pre_topc(sK7) != k2_tarski(k1_xboole_0,u1_struct_0(sK6))
    | v2_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(superposition,[],[f3787,f4255])).

fof(f4255,plain,(
    u1_struct_0(sK6) = u1_struct_0(sK7) ),
    inference(unit_resulting_resolution,[],[f3754,f3946,f3801])).

fof(f3801,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3632])).

fof(f3787,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3704])).

fof(f3753,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f3693])).

fof(f3756,plain,(
    ~ v2_tdlat_3(sK7) ),
    inference(cnf_transformation,[],[f3693])).
%------------------------------------------------------------------------------
