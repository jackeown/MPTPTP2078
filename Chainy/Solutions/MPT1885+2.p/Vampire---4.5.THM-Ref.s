%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1885+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:36 EST 2020

% Result     : Theorem 4.20s
% Output     : Refutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   84 (1061 expanded)
%              Number of leaves         :    9 ( 333 expanded)
%              Depth                    :   32
%              Number of atoms          :  480 (11105 expanded)
%              Number of equality atoms :   54 (1117 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20255,plain,(
    $false ),
    inference(subsumption_resolution,[],[f20254,f4284])).

fof(f4284,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f4064])).

fof(f4064,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK9
        | ~ v4_tex_2(X2,sK8)
        | ~ m1_pre_topc(X2,sK8)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & v3_tex_2(sK9,sK8)
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & ~ v1_xboole_0(sK9)
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f3738,f4063,f4062])).

fof(f4062,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( u1_struct_0(X2) != X1
                | ~ v4_tex_2(X2,X0)
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,sK8)
              | ~ m1_pre_topc(X2,sK8)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,sK8)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f4063,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( u1_struct_0(X2) != X1
            | ~ v4_tex_2(X2,sK8)
            | ~ m1_pre_topc(X2,sK8)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & v3_tex_2(X1,sK8)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
        & ~ v1_xboole_0(X1) )
   => ( ! [X2] :
          ( u1_struct_0(X2) != sK9
          | ~ v4_tex_2(X2,sK8)
          | ~ m1_pre_topc(X2,sK8)
          | ~ v1_pre_topc(X2)
          | v2_struct_0(X2) )
      & v3_tex_2(sK9,sK8)
      & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
      & ~ v1_xboole_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f3738,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3737])).

fof(f3737,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3708])).

fof(f3708,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f3707])).

fof(f3707,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).

fof(f20254,plain,(
    v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f20253,f4286])).

fof(f4286,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f4064])).

fof(f20253,plain,
    ( ~ l1_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f20252,f5871])).

fof(f5871,plain,(
    m1_pre_topc(sK55(sK8,sK9),sK8) ),
    inference(subsumption_resolution,[],[f5870,f4284])).

fof(f5870,plain,
    ( m1_pre_topc(sK55(sK8,sK9),sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5869,f4285])).

fof(f4285,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f4064])).

fof(f5869,plain,
    ( m1_pre_topc(sK55(sK8,sK9),sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5868,f4286])).

fof(f5868,plain,
    ( m1_pre_topc(sK55(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5867,f4287])).

fof(f4287,plain,(
    ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f4064])).

fof(f5867,plain,
    ( m1_pre_topc(sK55(sK8,sK9),sK8)
    | v1_xboole_0(sK9)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5807,f4288])).

fof(f4288,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f4064])).

fof(f5807,plain,
    ( m1_pre_topc(sK55(sK8,sK9),sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(sK9)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[],[f5369,f4555])).

fof(f4555,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK55(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4201])).

fof(f4201,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK55(X0,X1)) = X1
            & m1_pre_topc(sK55(X0,X1),X0)
            & v1_tdlat_3(sK55(X0,X1))
            & v1_pre_topc(sK55(X0,X1))
            & ~ v2_struct_0(sK55(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK55])],[f3909,f4200])).

fof(f4200,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK55(X0,X1)) = X1
        & m1_pre_topc(sK55(X0,X1),X0)
        & v1_tdlat_3(sK55(X0,X1))
        & v1_pre_topc(sK55(X0,X1))
        & ~ v2_struct_0(sK55(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3909,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3908])).

fof(f3908,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3686])).

fof(f3686,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f5369,plain,(
    v2_tex_2(sK9,sK8) ),
    inference(global_subsumption,[],[f4288,f5368])).

fof(f5368,plain,
    ( v2_tex_2(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(subsumption_resolution,[],[f5352,f4286])).

fof(f5352,plain,
    ( v2_tex_2(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8) ),
    inference(resolution,[],[f4289,f4354])).

fof(f4354,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4101])).

fof(f4101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK21(X0,X1) != X1
                & r1_tarski(X1,sK21(X0,X1))
                & v2_tex_2(sK21(X0,X1),X0)
                & m1_subset_1(sK21(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f4099,f4100])).

fof(f4100,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK21(X0,X1) != X1
        & r1_tarski(X1,sK21(X0,X1))
        & v2_tex_2(sK21(X0,X1),X0)
        & m1_subset_1(sK21(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4099,plain,(
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
    inference(rectify,[],[f4098])).

fof(f4098,plain,(
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
    inference(flattening,[],[f4097])).

fof(f4097,plain,(
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
    inference(nnf_transformation,[],[f3785])).

fof(f3785,plain,(
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
    inference(flattening,[],[f3784])).

fof(f3784,plain,(
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
    inference(ennf_transformation,[],[f3612])).

fof(f3612,axiom,(
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

fof(f4289,plain,(
    v3_tex_2(sK9,sK8) ),
    inference(cnf_transformation,[],[f4064])).

fof(f20252,plain,
    ( ~ m1_pre_topc(sK55(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f20251,f10529])).

fof(f10529,plain,(
    ~ v4_tex_2(sK55(sK8,sK9),sK8) ),
    inference(subsumption_resolution,[],[f10528,f5856])).

fof(f5856,plain,(
    ~ v2_struct_0(sK55(sK8,sK9)) ),
    inference(subsumption_resolution,[],[f5855,f4284])).

fof(f5855,plain,
    ( ~ v2_struct_0(sK55(sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5854,f4285])).

fof(f5854,plain,
    ( ~ v2_struct_0(sK55(sK8,sK9))
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5853,f4286])).

fof(f5853,plain,
    ( ~ v2_struct_0(sK55(sK8,sK9))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5852,f4287])).

fof(f5852,plain,
    ( ~ v2_struct_0(sK55(sK8,sK9))
    | v1_xboole_0(sK9)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5804,f4288])).

fof(f5804,plain,
    ( ~ v2_struct_0(sK55(sK8,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(sK9)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[],[f5369,f4552])).

fof(f4552,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK55(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4201])).

fof(f10528,plain,
    ( ~ v4_tex_2(sK55(sK8,sK9),sK8)
    | v2_struct_0(sK55(sK8,sK9)) ),
    inference(subsumption_resolution,[],[f10527,f5861])).

fof(f5861,plain,(
    v1_pre_topc(sK55(sK8,sK9)) ),
    inference(subsumption_resolution,[],[f5860,f4284])).

fof(f5860,plain,
    ( v1_pre_topc(sK55(sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5859,f4285])).

fof(f5859,plain,
    ( v1_pre_topc(sK55(sK8,sK9))
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5858,f4286])).

fof(f5858,plain,
    ( v1_pre_topc(sK55(sK8,sK9))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5857,f4287])).

fof(f5857,plain,
    ( v1_pre_topc(sK55(sK8,sK9))
    | v1_xboole_0(sK9)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5805,f4288])).

fof(f5805,plain,
    ( v1_pre_topc(sK55(sK8,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(sK9)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[],[f5369,f4553])).

fof(f4553,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK55(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4201])).

fof(f10527,plain,
    ( ~ v4_tex_2(sK55(sK8,sK9),sK8)
    | ~ v1_pre_topc(sK55(sK8,sK9))
    | v2_struct_0(sK55(sK8,sK9)) ),
    inference(subsumption_resolution,[],[f10526,f5871])).

fof(f10526,plain,
    ( ~ v4_tex_2(sK55(sK8,sK9),sK8)
    | ~ m1_pre_topc(sK55(sK8,sK9),sK8)
    | ~ v1_pre_topc(sK55(sK8,sK9))
    | v2_struct_0(sK55(sK8,sK9)) ),
    inference(trivial_inequality_removal,[],[f10172])).

fof(f10172,plain,
    ( sK9 != sK9
    | ~ v4_tex_2(sK55(sK8,sK9),sK8)
    | ~ m1_pre_topc(sK55(sK8,sK9),sK8)
    | ~ v1_pre_topc(sK55(sK8,sK9))
    | v2_struct_0(sK55(sK8,sK9)) ),
    inference(superposition,[],[f4290,f5876])).

fof(f5876,plain,(
    sK9 = u1_struct_0(sK55(sK8,sK9)) ),
    inference(subsumption_resolution,[],[f5875,f4284])).

fof(f5875,plain,
    ( sK9 = u1_struct_0(sK55(sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5874,f4285])).

fof(f5874,plain,
    ( sK9 = u1_struct_0(sK55(sK8,sK9))
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5873,f4286])).

fof(f5873,plain,
    ( sK9 = u1_struct_0(sK55(sK8,sK9))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5872,f4287])).

fof(f5872,plain,
    ( sK9 = u1_struct_0(sK55(sK8,sK9))
    | v1_xboole_0(sK9)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f5808,f4288])).

fof(f5808,plain,
    ( sK9 = u1_struct_0(sK55(sK8,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(sK9)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[],[f5369,f4556])).

fof(f4556,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK55(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4201])).

fof(f4290,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK9
      | ~ v4_tex_2(X2,sK8)
      | ~ m1_pre_topc(X2,sK8)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f4064])).

fof(f20251,plain,
    ( v4_tex_2(sK55(sK8,sK9),sK8)
    | ~ m1_pre_topc(sK55(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f20250,f4289])).

fof(f20250,plain,
    ( ~ v3_tex_2(sK9,sK8)
    | v4_tex_2(sK55(sK8,sK9),sK8)
    | ~ m1_pre_topc(sK55(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(superposition,[],[f4306,f10608])).

fof(f10608,plain,(
    sK9 = sK11(sK8,sK55(sK8,sK9)) ),
    inference(forward_demodulation,[],[f10607,f5876])).

fof(f10607,plain,(
    u1_struct_0(sK55(sK8,sK9)) = sK11(sK8,sK55(sK8,sK9)) ),
    inference(subsumption_resolution,[],[f10606,f4284])).

fof(f10606,plain,
    ( u1_struct_0(sK55(sK8,sK9)) = sK11(sK8,sK55(sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f10605,f4286])).

fof(f10605,plain,
    ( u1_struct_0(sK55(sK8,sK9)) = sK11(sK8,sK55(sK8,sK9))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f10598,f5871])).

fof(f10598,plain,
    ( u1_struct_0(sK55(sK8,sK9)) = sK11(sK8,sK55(sK8,sK9))
    | ~ m1_pre_topc(sK55(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[],[f10529,f4305])).

fof(f4305,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | u1_struct_0(X1) = sK11(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4075])).

fof(f4075,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK11(X0,X1),X0)
                & u1_struct_0(X1) = sK11(X0,X1)
                & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f4073,f4074])).

fof(f4074,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK11(X0,X1),X0)
        & u1_struct_0(X1) = sK11(X0,X1)
        & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4073,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4072])).

fof(f4072,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_tex_2(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3744])).

fof(f3744,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3743])).

fof(f3743,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3613])).

fof(f3613,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

fof(f4306,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(sK11(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4075])).
%------------------------------------------------------------------------------
