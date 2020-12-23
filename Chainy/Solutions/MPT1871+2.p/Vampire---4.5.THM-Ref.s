%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1871+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:36 EST 2020

% Result     : Theorem 6.26s
% Output     : Refutation 6.26s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 955 expanded)
%              Number of leaves         :   10 ( 404 expanded)
%              Depth                    :   11
%              Number of atoms          :  335 (10274 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12976,plain,(
    $false ),
    inference(global_subsumption,[],[f5076,f12975])).

fof(f12975,plain,(
    ~ v4_pre_topc(k2_xboole_0(sK14(sK0),sK15(sK0)),sK0) ),
    inference(forward_demodulation,[],[f12970,f5144])).

fof(f5144,plain,(
    k4_subset_1(u1_struct_0(sK0),sK14(sK0),sK15(sK0)) = k2_xboole_0(sK14(sK0),sK15(sK0)) ),
    inference(unit_resulting_resolution,[],[f4181,f4182,f3844])).

fof(f3844,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3696])).

fof(f3696,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f3695])).

fof(f3695,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f491])).

fof(f491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f4182,plain,(
    m1_subset_1(sK15(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f3835,f3841,f3839,f3840,f3838,f3836,f3837,f3842,f3899])).

fof(f3899,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3805])).

fof(f3805,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK14(X0),sK15(X0)),X0)
          | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK14(X0),sK15(X0)),X0) )
        & v4_pre_topc(sK15(X0),X0)
        & v4_pre_topc(sK14(X0),X0)
        & m1_subset_1(sK15(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK14(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f3802,f3804,f3803])).

fof(f3803,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
              & v4_pre_topc(X4,X0)
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X4] :
            ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK14(X0),X4),X0)
              | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK14(X0),X4),X0) )
            & v4_pre_topc(X4,X0)
            & v4_pre_topc(sK14(X0),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK14(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3804,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK14(X0),X4),X0)
            | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK14(X0),X4),X0) )
          & v4_pre_topc(X4,X0)
          & v4_pre_topc(sK14(X0),X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK14(X0),sK15(X0)),X0)
          | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK14(X0),sK15(X0)),X0) )
        & v4_pre_topc(sK15(X0),X0)
        & v4_pre_topc(sK14(X0),X0)
        & m1_subset_1(sK15(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3802,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X3] :
          ( ? [X4] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
              & v4_pre_topc(X4,X0)
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f3742])).

fof(f3742,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v4_pre_topc(X4,X0)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3741])).

fof(f3741,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v4_pre_topc(X4,X0)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3690])).

fof(f3690,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => ( v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X4,X0)
                    & v2_tex_2(X3,X0)
                    & v4_pre_topc(X4,X0)
                    & v4_pre_topc(X3,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ) ) ) ) ),
    inference(rectify,[],[f3674])).

fof(f3674,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => ( v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tex_2)).

fof(f3842,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f3773])).

fof(f3773,plain,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_tex_2(sK2,sK0)
    & v2_tex_2(sK1,sK0)
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3692,f3772,f3771,f3770])).

fof(f3770,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_tex_2(X2,X0)
                & v2_tex_2(X1,X0)
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_tex_2(X2,sK0)
              & v2_tex_2(X1,sK0)
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3771,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v2_tex_2(X2,sK0)
            & v2_tex_2(X1,sK0)
            & v4_pre_topc(X2,sK0)
            & v4_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v2_tex_2(X2,sK0)
          & v2_tex_2(sK1,sK0)
          & v4_pre_topc(X2,sK0)
          & v4_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3772,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v2_tex_2(X2,sK0)
        & v2_tex_2(sK1,sK0)
        & v4_pre_topc(X2,sK0)
        & v4_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v2_tex_2(sK2,sK0)
      & v2_tex_2(sK1,sK0)
      & v4_pre_topc(sK2,sK0)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3692,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3691])).

fof(f3691,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3683])).

fof(f3683,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3682])).

fof(f3682,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  & v2_tex_2(X1,X0)
                  & v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tex_2)).

fof(f3837,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3773])).

fof(f3836,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3773])).

fof(f3838,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3773])).

fof(f3840,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f3773])).

fof(f3839,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3773])).

fof(f3841,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f3773])).

fof(f3835,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3773])).

fof(f4181,plain,(
    m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f3835,f3841,f3839,f3840,f3838,f3836,f3837,f3842,f3898])).

fof(f3898,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK14(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3805])).

fof(f12970,plain,(
    ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK14(sK0),sK15(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f3835,f3840,f3841,f3838,f3839,f3836,f3837,f3842,f5109,f3902])).

fof(f3902,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK14(X0),sK15(X0)),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK14(X0),sK15(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3805])).

fof(f5109,plain,(
    v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK14(sK0),sK15(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f3834,f3835,f4184,f4183,f4181,f4182,f3916])).

fof(f3916,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3754,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3753])).

fof(f3753,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2151])).

fof(f2151,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

fof(f4183,plain,(
    v4_pre_topc(sK14(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f3835,f3839,f3840,f3841,f3838,f3836,f3837,f3842,f3900])).

fof(f3900,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK14(X0),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3805])).

fof(f4184,plain,(
    v4_pre_topc(sK15(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f3835,f3839,f3840,f3841,f3838,f3836,f3837,f3842,f3901])).

fof(f3901,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK15(X0),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3805])).

fof(f3834,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3773])).

fof(f5076,plain,(
    v4_pre_topc(k2_xboole_0(sK14(sK0),sK15(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f3834,f3835,f4183,f4181,f4184,f4182,f3903])).

fof(f3903,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f3744])).

fof(f3744,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3743])).

fof(f3743,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2115])).

fof(f2115,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tops_1)).
%------------------------------------------------------------------------------
