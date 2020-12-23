%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1852+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 201 expanded)
%              Number of leaves         :    7 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  146 ( 999 expanded)
%              Number of equality atoms :   22 ( 184 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4228,plain,(
    $false ),
    inference(global_subsumption,[],[f4013,f4226])).

fof(f4226,plain,(
    r2_hidden(k6_subset_1(u1_struct_0(sK4),sK10(sK5)),u1_pre_topc(sK4)) ),
    inference(unit_resulting_resolution,[],[f3747,f3750,f4049,f3985,f3771])).

fof(f3771,plain,(
    ! [X2,X0] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3707])).

fof(f3707,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
            & r2_hidden(sK10(X0),u1_pre_topc(X0))
            & m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f3705,f3706])).

fof(f3706,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
        & r2_hidden(sK10(X0),u1_pre_topc(X0))
        & m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3705,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f3704])).

fof(f3704,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3625])).

fof(f3625,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3624])).

fof(f3624,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3573])).

fof(f3573,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(f3985,plain,(
    m1_subset_1(sK10(sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(superposition,[],[f3921,f3983])).

fof(f3983,plain,(
    u1_struct_0(sK4) = u1_struct_0(sK5) ),
    inference(unit_resulting_resolution,[],[f3749,f3904,f3787])).

fof(f3787,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3638])).

fof(f3638,plain,(
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

fof(f3904,plain,(
    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unit_resulting_resolution,[],[f3747,f3876])).

fof(f3876,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3686])).

fof(f3686,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3749,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(cnf_transformation,[],[f3695])).

fof(f3695,plain,
    ( ~ v3_tdlat_3(sK5)
    & v3_tdlat_3(sK4)
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
    & l1_pre_topc(sK5)
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f3623,f3694,f3693])).

fof(f3693,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tdlat_3(X1)
            & v3_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(sK4)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3694,plain,
    ( ? [X1] :
        ( ~ v3_tdlat_3(X1)
        & v3_tdlat_3(sK4)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        & l1_pre_topc(X1) )
   => ( ~ v3_tdlat_3(sK5)
      & v3_tdlat_3(sK4)
      & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f3623,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3622])).

fof(f3622,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3612])).

fof(f3612,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3611])).

fof(f3611,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

fof(f3921,plain,(
    m1_subset_1(sK10(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unit_resulting_resolution,[],[f3748,f3751,f3772])).

fof(f3772,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3707])).

fof(f3751,plain,(
    ~ v3_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f3695])).

fof(f3748,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f3695])).

fof(f4049,plain,(
    r2_hidden(sK10(sK5),u1_pre_topc(sK4)) ),
    inference(superposition,[],[f3922,f3984])).

fof(f3984,plain,(
    u1_pre_topc(sK4) = u1_pre_topc(sK5) ),
    inference(unit_resulting_resolution,[],[f3749,f3904,f3788])).

fof(f3788,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3638])).

fof(f3922,plain,(
    r2_hidden(sK10(sK5),u1_pre_topc(sK5)) ),
    inference(unit_resulting_resolution,[],[f3748,f3751,f3773])).

fof(f3773,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),u1_pre_topc(X0))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3707])).

fof(f3750,plain,(
    v3_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f3695])).

fof(f3747,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3695])).

fof(f4013,plain,(
    ~ r2_hidden(k6_subset_1(u1_struct_0(sK4),sK10(sK5)),u1_pre_topc(sK4)) ),
    inference(global_subsumption,[],[f3751,f3748,f4012])).

fof(f4012,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK4),sK10(sK5)),u1_pre_topc(sK4))
    | v3_tdlat_3(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(forward_demodulation,[],[f3989,f3984])).

fof(f3989,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK4),sK10(sK5)),u1_pre_topc(sK5))
    | v3_tdlat_3(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(superposition,[],[f3774,f3983])).

fof(f3774,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3707])).
%------------------------------------------------------------------------------
