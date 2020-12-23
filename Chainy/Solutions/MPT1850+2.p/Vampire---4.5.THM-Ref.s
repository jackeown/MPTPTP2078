%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1850+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   32 (  93 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 423 expanded)
%              Number of equality atoms :   32 ( 106 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4273,plain,(
    $false ),
    inference(global_subsumption,[],[f4241,f4272])).

fof(f4272,plain,(
    u1_pre_topc(sK6) != u1_pre_topc(sK7) ),
    inference(forward_demodulation,[],[f4242,f3979])).

fof(f3979,plain,(
    u1_pre_topc(sK6) = k9_setfam_1(u1_struct_0(sK6)) ),
    inference(unit_resulting_resolution,[],[f3749,f3752,f3783])).

fof(f3783,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3701])).

fof(f3701,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3618])).

fof(f3618,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3570])).

fof(f3570,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(f3752,plain,(
    v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f3690])).

fof(f3690,plain,
    ( ~ v1_tdlat_3(sK7)
    & v1_tdlat_3(sK6)
    & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
    & l1_pre_topc(sK7)
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f3617,f3689,f3688])).

fof(f3688,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tdlat_3(X1)
            & v1_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(sK6)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f3689,plain,
    ( ? [X1] :
        ( ~ v1_tdlat_3(X1)
        & v1_tdlat_3(sK6)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
        & l1_pre_topc(X1) )
   => ( ~ v1_tdlat_3(sK7)
      & v1_tdlat_3(sK6)
      & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
      & l1_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f3617,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3616])).

fof(f3616,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3606])).

fof(f3606,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3605])).

fof(f3605,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

fof(f3749,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f3690])).

fof(f4242,plain,(
    u1_pre_topc(sK7) != k9_setfam_1(u1_struct_0(sK6)) ),
    inference(superposition,[],[f3982,f4240])).

fof(f4240,plain,(
    u1_struct_0(sK6) = u1_struct_0(sK7) ),
    inference(unit_resulting_resolution,[],[f3751,f3943,f3798])).

fof(f3798,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3629])).

fof(f3629,plain,(
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

fof(f3943,plain,(
    m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(unit_resulting_resolution,[],[f3749,f3900])).

fof(f3900,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3678])).

fof(f3678,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3751,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) ),
    inference(cnf_transformation,[],[f3690])).

fof(f3982,plain,(
    u1_pre_topc(sK7) != k9_setfam_1(u1_struct_0(sK7)) ),
    inference(unit_resulting_resolution,[],[f3750,f3753,f3784])).

fof(f3784,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3701])).

fof(f3753,plain,(
    ~ v1_tdlat_3(sK7) ),
    inference(cnf_transformation,[],[f3690])).

fof(f3750,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f3690])).

fof(f4241,plain,(
    u1_pre_topc(sK6) = u1_pre_topc(sK7) ),
    inference(unit_resulting_resolution,[],[f3751,f3943,f3799])).

fof(f3799,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3629])).
%------------------------------------------------------------------------------
