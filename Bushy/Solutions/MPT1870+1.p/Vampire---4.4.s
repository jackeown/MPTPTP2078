%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t38_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:32 EDT 2019

% Result     : Theorem 36.59s
% Output     : Refutation 36.59s
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
fof(f13832,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13831,f469])).

fof(f469,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f379,plain,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_tex_2(sK2,sK0)
    & v2_tex_2(sK1,sK0)
    & v3_pre_topc(sK2,sK0)
    & v3_pre_topc(sK1,sK0)
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
                & v3_pre_topc(X2,X0)
                & v3_pre_topc(X1,X0)
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
              & v3_pre_topc(X2,sK0)
              & v3_pre_topc(X1,sK0)
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
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v2_tex_2(X2,X0)
            & v2_tex_2(sK1,X0)
            & v3_pre_topc(X2,X0)
            & v3_pre_topc(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f378,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v2_tex_2(X2,X0)
          & v2_tex_2(X1,X0)
          & v3_pre_topc(X2,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v2_tex_2(sK2,X0)
        & v2_tex_2(X1,X0)
        & v3_pre_topc(sK2,X0)
        & v3_pre_topc(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f176,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
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
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
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
                    & v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
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
                  & v3_pre_topc(X2,X0)
                  & v3_pre_topc(X1,X0) )
               => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t38_tex_2.p',t38_tex_2)).

fof(f13831,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13830,f470])).

fof(f470,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f13830,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13829,f2034])).

fof(f2034,plain,(
    v3_pre_topc(sK7(sK0),sK0) ),
    inference(subsumption_resolution,[],[f2033,f470])).

fof(f2033,plain,
    ( v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2032,f471])).

fof(f471,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f379])).

fof(f2032,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2031,f472])).

fof(f472,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f379])).

fof(f2031,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2030,f473])).

fof(f473,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f2030,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2029,f474])).

fof(f474,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f2029,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2028,f475])).

fof(f475,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f2028,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2019,f476])).

fof(f476,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f379])).

fof(f2019,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK7(sK0),sK0)
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
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK7(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).

fof(f391,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK7(X0),sK8(X0)),X0)
          | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK7(X0),sK8(X0)),X0) )
        & v3_pre_topc(sK8(X0),X0)
        & v3_pre_topc(sK7(X0),X0)
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f388,f390,f389])).

fof(f389,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
              & v3_pre_topc(X4,X0)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X4] :
            ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK7(X0),X4),X0)
              | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK7(X0),X4),X0) )
            & v3_pre_topc(X4,X0)
            & v3_pre_topc(sK7(X0),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f390,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
            | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
          & v3_pre_topc(X4,X0)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X3,sK8(X0)),X0)
          | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X3,sK8(X0)),X0) )
        & v3_pre_topc(sK8(X0),X0)
        & v3_pre_topc(X3,X0)
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f388,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X3] :
          ( ? [X4] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
              & v3_pre_topc(X4,X0)
              & v3_pre_topc(X3,X0)
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
              | ~ v3_pre_topc(X4,X0)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
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
              | ~ v3_pre_topc(X4,X0)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
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
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X4,X0)
                    & v2_tex_2(X3,X0)
                    & v3_pre_topc(X4,X0)
                    & v3_pre_topc(X3,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ) ) ) ) ),
    inference(rectify,[],[f153])).

fof(f153,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t38_tex_2.p',t30_tex_2)).

fof(f13829,plain,
    ( ~ v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13828,f2066])).

fof(f2066,plain,(
    m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2065,f470])).

fof(f2065,plain,
    ( m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2064,f471])).

fof(f2064,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2063,f472])).

fof(f2063,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2062,f473])).

fof(f2062,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2061,f474])).

fof(f2061,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2060,f475])).

fof(f2060,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2051,f476])).

fof(f2051,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
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
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).

fof(f13828,plain,
    ( ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13827,f2050])).

fof(f2050,plain,(
    v3_pre_topc(sK8(sK0),sK0) ),
    inference(subsumption_resolution,[],[f2049,f470])).

fof(f2049,plain,
    ( v3_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2048,f471])).

fof(f2048,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2047,f472])).

fof(f2047,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2046,f473])).

fof(f2046,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2045,f474])).

fof(f2045,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2044,f475])).

fof(f2044,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2035,f476])).

fof(f2035,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK8(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f545,f477])).

fof(f545,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK8(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).

fof(f13827,plain,
    ( ~ v3_pre_topc(sK8(sK0),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13820,f2128])).

fof(f2128,plain,(
    m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2127,f470])).

fof(f2127,plain,
    ( m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2126,f471])).

fof(f2126,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2125,f472])).

fof(f2125,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2124,f473])).

fof(f2124,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2123,f474])).

fof(f2123,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2122,f475])).

fof(f2122,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2113,f476])).

fof(f2113,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
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
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).

fof(f13820,plain,
    ( ~ m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK8(sK0),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f13809,f679])).

fof(f679,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f362])).

fof(f362,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f361])).

fof(f361,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t38_tex_2.p',fc7_tops_1)).

fof(f13809,plain,(
    ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f13808,f469])).

fof(f13808,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13807,f470])).

fof(f13807,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13806,f2034])).

fof(f13806,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13805,f2066])).

fof(f13805,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13804,f2050])).

fof(f13804,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(sK8(sK0),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13798,f2128])).

fof(f13798,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ m1_subset_1(sK8(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK8(sK0),sK0)
    | ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK7(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f13796,f680])).

fof(f680,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f364])).

fof(f364,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f363])).

fof(f363,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t38_tex_2.p',fc6_tops_1)).

fof(f13796,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f13795,f470])).

fof(f13795,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13794,f471])).

fof(f13794,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13793,f472])).

fof(f13793,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13792,f473])).

fof(f13792,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13791,f474])).

fof(f13791,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13790,f475])).

fof(f13790,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f13779,f476])).

fof(f13779,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK7(sK0),sK8(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f7230,f477])).

fof(f7230,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X2,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_xboole_0(sK7(X0),sK8(X0)),X0)
      | ~ v3_pre_topc(k2_xboole_0(sK7(X0),sK8(X0)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f7229,f662])).

fof(f662,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t38_tex_2.p',commutativity_k2_xboole_0)).

fof(f7229,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k2_xboole_0(sK8(X0),sK7(X0)),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_xboole_0(sK7(X0),sK8(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X2,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f7228,f543])).

fof(f7228,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k2_xboole_0(sK8(X0),sK7(X0)),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_xboole_0(sK7(X0),sK8(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X2,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f7223,f542])).

fof(f7223,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k2_xboole_0(sK8(X0),sK7(X0)),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_xboole_0(sK7(X0),sK8(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X2,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f2176,f1810])).

fof(f1810,plain,(
    ! [X10,X8,X9] :
      ( k4_subset_1(X8,X10,X9) = k2_xboole_0(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ),
    inference(duplicate_literal_removal,[],[f1799])).

fof(f1799,plain,(
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
    file('/export/starexec/sandbox/benchmark/tex_2__t38_tex_2.p',redefinition_k4_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/tex_2__t38_tex_2.p',commutativity_k4_subset_1)).

fof(f2176,plain,(
    ! [X4,X2,X3] :
      ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X2),sK7(X2),sK8(X2)),X2)
      | ~ v2_tex_2(X3,X2)
      | ~ v2_tex_2(X4,X2)
      | ~ v3_pre_topc(X3,X2)
      | ~ v3_pre_topc(X4,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(k3_xboole_0(sK7(X2),sK8(X2)),X2)
      | v2_tex_2(k4_subset_1(u1_struct_0(X2),X4,X3),X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f2175,f543])).

fof(f2175,plain,(
    ! [X4,X2,X3] :
      ( ~ v3_pre_topc(k3_xboole_0(sK7(X2),sK8(X2)),X2)
      | ~ v2_tex_2(X3,X2)
      | ~ v2_tex_2(X4,X2)
      | ~ v3_pre_topc(X3,X2)
      | ~ v3_pre_topc(X4,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(k4_subset_1(u1_struct_0(X2),sK7(X2),sK8(X2)),X2)
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
    file('/export/starexec/sandbox/benchmark/tex_2__t38_tex_2.p',redefinition_k9_subset_1)).

fof(f546,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK7(X0),sK8(X0)),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK7(X0),sK8(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f391])).
%------------------------------------------------------------------------------
