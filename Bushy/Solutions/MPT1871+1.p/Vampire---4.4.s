%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t39_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:32 EDT 2019

% Result     : Theorem 36.65s
% Output     : Refutation 36.65s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 907 expanded)
%              Number of leaves         :   13 ( 346 expanded)
%              Depth                    :   34
%              Number of atoms          :  655 (9295 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14032,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14031,f469])).

fof(f469,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f379,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f176,f378,f377,f376])).

fof(f376,plain,
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

fof(f377,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v2_tex_2(X2,X0)
            & v2_tex_2(sK1,X0)
            & v4_pre_topc(X2,X0)
            & v4_pre_topc(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f378,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v2_tex_2(X2,X0)
          & v2_tex_2(X1,X0)
          & v4_pre_topc(X2,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v2_tex_2(sK2,X0)
        & v2_tex_2(X1,X0)
        & v4_pre_topc(sK2,X0)
        & v4_pre_topc(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f176,plain,(
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
    inference(flattening,[],[f175])).

fof(f175,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t39_tex_2.p',t39_tex_2)).

fof(f14031,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f14030,f470])).

fof(f470,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f14030,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f14029,f2031])).

fof(f2031,plain,(
    v4_pre_topc(sK7(sK0),sK0) ),
    inference(subsumption_resolution,[],[f2030,f470])).

fof(f2030,plain,
    ( v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2029,f471])).

fof(f471,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f379])).

fof(f2029,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2028,f472])).

fof(f472,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f379])).

fof(f2028,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2027,f473])).

fof(f473,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f2027,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2026,f474])).

fof(f474,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f2026,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2025,f475])).

fof(f475,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f2025,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2016,f476])).

fof(f476,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f2016,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f544,f477])).

fof(f477,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f544,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(sK7(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).

fof(f391,plain,(
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
      | ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK7(X0),sK8(X0)),X0)
          | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK7(X0),sK8(X0)),X0) )
        & v4_pre_topc(sK8(X0),X0)
        & v4_pre_topc(sK7(X0),X0)
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f388,f390,f389])).

fof(f389,plain,(
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
            ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK7(X0),X4),X0)
              | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK7(X0),X4),X0) )
            & v4_pre_topc(X4,X0)
            & v4_pre_topc(sK7(X0),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f390,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
            | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
          & v4_pre_topc(X4,X0)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,sK8(X0)),X0)
          | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,sK8(X0)),X0) )
        & v4_pre_topc(sK8(X0),X0)
        & v4_pre_topc(X3,X0)
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f388,plain,(
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
    inference(rectify,[],[f233])).

fof(f233,plain,(
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
    inference(flattening,[],[f232])).

fof(f232,plain,(
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
    inference(ennf_transformation,[],[f160])).

fof(f160,plain,(
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
    inference(rectify,[],[f153])).

fof(f153,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t39_tex_2.p',t31_tex_2)).

fof(f14029,plain,
    ( ~ v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f14028,f2063])).

fof(f2063,plain,(
    m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2062,f470])).

fof(f2062,plain,
    ( m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2061,f471])).

fof(f2061,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2060,f472])).

fof(f2060,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2059,f473])).

fof(f2059,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2058,f474])).

fof(f2058,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2057,f475])).

fof(f2057,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2048,f476])).

fof(f2048,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f542,f477])).

fof(f542,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).

fof(f14028,plain,
    ( ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f14027,f2047])).

fof(f2047,plain,(
    v4_pre_topc(sK8(sK0),sK0) ),
    inference(subsumption_resolution,[],[f2046,f470])).

fof(f2046,plain,
    ( v4_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2045,f471])).

fof(f2045,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2044,f472])).

fof(f2044,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2043,f473])).

fof(f2043,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2042,f474])).

fof(f2042,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2041,f475])).

fof(f2041,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2032,f476])).

fof(f2032,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f545,f477])).

fof(f545,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(sK8(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).

fof(f14027,plain,
    ( ~ v4_pre_topc(sK8(sK0),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f14020,f2122])).

fof(f2122,plain,(
    m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2121,f470])).

fof(f2121,plain,
    ( m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2120,f471])).

fof(f2120,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2119,f472])).

fof(f2119,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2118,f473])).

fof(f2118,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2117,f474])).

fof(f2117,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2116,f475])).

fof(f2116,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2107,f476])).

fof(f2107,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f543,f477])).

fof(f543,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).

fof(f14020,plain,
    ( ~ m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK8(sK0),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f14009,f679])).

fof(f679,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f362])).

fof(f362,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f361])).

fof(f361,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f96])).

fof(f96,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t39_tex_2.p',fc5_tops_1)).

fof(f14009,plain,(
    ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f14008,f469])).

fof(f14008,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f14007,f470])).

fof(f14007,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f14006,f2031])).

fof(f14006,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f14005,f2063])).

fof(f14005,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f14004,f2047])).

fof(f14004,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(sK8(sK0),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13998,f2122])).

fof(f13998,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK8(sK0),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f13996,f680])).

fof(f680,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f364])).

fof(f364,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f363])).

fof(f363,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f94])).

fof(f94,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t39_tex_2.p',fc4_tops_1)).

fof(f13996,plain,
    ( ~ v4_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f13995,f470])).

fof(f13995,plain,
    ( ~ v4_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13994,f471])).

fof(f13994,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13993,f472])).

fof(f13993,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13992,f473])).

fof(f13992,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13991,f474])).

fof(f13991,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13990,f475])).

fof(f13990,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13979,f476])).

fof(f13979,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v4_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f7281,f477])).

fof(f7281,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X2,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k3_xboole_0(sK7(X0),sK8(X0)),X0)
      | ~ v4_pre_topc(k2_xboole_0(sK7(X0),sK8(X0)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f7280,f662])).

fof(f662,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t39_tex_2.p',commutativity_k2_xboole_0)).

fof(f7280,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k2_xboole_0(sK8(X0),sK7(X0)),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k3_xboole_0(sK7(X0),sK8(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X2,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f7279,f543])).

fof(f7279,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k2_xboole_0(sK8(X0),sK7(X0)),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k3_xboole_0(sK7(X0),sK8(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X2,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f7274,f542])).

fof(f7274,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k2_xboole_0(sK8(X0),sK7(X0)),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k3_xboole_0(sK7(X0),sK8(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X2,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f2167,f1808])).

fof(f1808,plain,(
    ! [X10,X8,X9] :
      ( k4_subset_1(X8,X10,X9) = k2_xboole_0(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ),
    inference(duplicate_literal_removal,[],[f1797])).

fof(f1797,plain,(
    ! [X10,X8,X9] :
      ( k4_subset_1(X8,X10,X9) = k2_xboole_0(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ),
    inference(superposition,[],[f685,f684])).

fof(f684,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f372])).

fof(f372,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f371])).

fof(f371,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f147])).

fof(f147,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t39_tex_2.p',redefinition_k4_subset_1)).

fof(f685,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f374])).

fof(f374,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f373])).

fof(f373,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t39_tex_2.p',commutativity_k4_subset_1)).

fof(f2167,plain,(
    ! [X4,X2,X3] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X2),sK7(X2),sK8(X2)),X2)
      | ~ v2_tex_2(X3,X2)
      | ~ v2_tex_2(X4,X2)
      | ~ v4_pre_topc(X3,X2)
      | ~ v4_pre_topc(X4,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(k3_xboole_0(sK7(X2),sK8(X2)),X2)
      | v2_tex_2(k4_subset_1(u1_struct_0(X2),X4,X3),X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f2166,f543])).

fof(f2166,plain,(
    ! [X4,X2,X3] :
      ( ~ v4_pre_topc(k3_xboole_0(sK7(X2),sK8(X2)),X2)
      | ~ v2_tex_2(X3,X2)
      | ~ v2_tex_2(X4,X2)
      | ~ v4_pre_topc(X3,X2)
      | ~ v4_pre_topc(X4,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X2),sK7(X2),sK8(X2)),X2)
      | v2_tex_2(k4_subset_1(u1_struct_0(X2),X4,X3),X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(sK8(X2),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f546,f675])).

fof(f675,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f355])).

fof(f355,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t39_tex_2.p',redefinition_k9_subset_1)).

fof(f546,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK7(X0),sK8(X0)),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK7(X0),sK8(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).
%------------------------------------------------------------------------------
