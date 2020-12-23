%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1871+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:44 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 364 expanded)
%              Number of clauses        :   78 (  97 expanded)
%              Number of leaves         :   13 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          :  726 (3163 expanded)
%              Number of equality atoms :   56 (  70 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f19,plain,(
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
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v2_tex_2(X2,X0)
          & v2_tex_2(X1,X0)
          & v4_pre_topc(X2,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,sK4),X0)
        & v2_tex_2(sK4,X0)
        & v2_tex_2(X1,X0)
        & v4_pre_topc(sK4,X0)
        & v4_pre_topc(X1,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
            ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),sK3,X2),X0)
            & v2_tex_2(X2,X0)
            & v2_tex_2(sK3,X0)
            & v4_pre_topc(X2,X0)
            & v4_pre_topc(sK3,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
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
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK2),X1,X2),sK2)
              & v2_tex_2(X2,sK2)
              & v2_tex_2(X1,sK2)
              & v4_pre_topc(X2,sK2)
              & v4_pre_topc(X1,sK2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    & v2_tex_2(sK4,sK2)
    & v2_tex_2(sK3,sK2)
    & v4_pre_topc(sK4,sK2)
    & v4_pre_topc(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f27,f26,f25])).

fof(f38,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(rectify,[],[f5])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f21,plain,(
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
    inference(rectify,[],[f18])).

fof(f23,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
            | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
          & v4_pre_topc(X4,X0)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,sK1(X0)),X0)
          | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,sK1(X0)),X0) )
        & v4_pre_topc(sK1(X0),X0)
        & v4_pre_topc(X3,X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
            ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK0(X0),X4),X0)
              | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK0(X0),X4),X0) )
            & v4_pre_topc(X4,X0)
            & v4_pre_topc(sK0(X0),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
      | ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK0(X0),sK1(X0)),X0)
          | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK0(X0),sK1(X0)),X0) )
        & v4_pre_topc(sK1(X0),X0)
        & v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK0(X0),sK1(X0)),X0)
      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK0(X0),sK1(X0)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(sK1(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(sK0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    v2_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v4_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k2_xboole_0(X2,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k2_xboole_0(X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X1,sK2)
    | v4_pre_topc(k2_xboole_0(X0,X1),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_198,plain,
    ( v4_pre_topc(k2_xboole_0(X0,X1),sK2)
    | ~ v4_pre_topc(X1,sK2)
    | ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_194,c_16])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X1,sK2)
    | v4_pre_topc(k2_xboole_0(X0,X1),sK2) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0_44,sK2)
    | ~ v4_pre_topc(X1_44,sK2)
    | v4_pre_topc(k2_xboole_0(X0_44,X1_44),sK2) ),
    inference(subtyping,[status(esa)],[c_199])).

cnf(c_2548,plain,
    ( ~ m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k2_xboole_0(sK0(sK2),sK1(sK2)),sK2)
    | ~ v4_pre_topc(sK1(sK2),sK2)
    | ~ v4_pre_topc(sK0(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_574,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_905,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_575,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_904,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(X0_46))
    | k4_subset_1(X0_46,X1_44,X0_44) = k2_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_897,plain,
    ( k4_subset_1(X0_46,X0_44,X1_44) = k2_xboole_0(X0_44,X1_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(X0_46)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_1291,plain,
    ( k4_subset_1(u1_struct_0(sK2),X0_44,sK4) = k2_xboole_0(X0_44,sK4)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_897])).

cnf(c_1381,plain,
    ( k4_subset_1(u1_struct_0(sK2),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_905,c_1291])).

cnf(c_4,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X1),sK0(X1),sK1(X1)),X1)
    | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK0(X1),sK1(X1)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_379,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X1),sK0(X1),sK1(X1)),X1)
    | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK0(X1),sK1(X1)),X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_380,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X1,sK2)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2)
    | ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_567,plain,
    ( ~ v2_tex_2(X0_44,sK2)
    | ~ v2_tex_2(X1_44,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0_44,X1_44),sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0_44,sK2)
    | ~ v4_pre_topc(X1_44,sK2)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2)
    | ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2) ),
    inference(subtyping,[status(esa)],[c_380])).

cnf(c_583,plain,
    ( ~ v2_tex_2(X0_44,sK2)
    | ~ v2_tex_2(X1_44,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0_44,X1_44),sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0_44,sK2)
    | ~ v4_pre_topc(X1_44,sK2)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_567])).

cnf(c_913,plain,
    ( v2_tex_2(X0_44,sK2) != iProver_top
    | v2_tex_2(X1_44,sK2) != iProver_top
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0_44,X1_44),sK2) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(X0_44,sK2) != iProver_top
    | v4_pre_topc(X1_44,sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_2073,plain,
    ( v2_tex_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
    | v2_tex_2(sK4,sK2) != iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(sK4,sK2) != iProver_top
    | v4_pre_topc(sK3,sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_913])).

cnf(c_2129,plain,
    ( v2_tex_2(k2_xboole_0(sK3,sK4),sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(sK4,sK2)
    | ~ v4_pre_topc(sK3,sK2)
    | ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2073])).

cnf(c_1142,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | k4_subset_1(u1_struct_0(sK2),X0_44,sK1(sK2)) = k2_xboole_0(X0_44,sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_2037,plain,
    ( ~ m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | k4_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)) = k2_xboole_0(sK0(sK2),sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_588,plain,
    ( ~ v4_pre_topc(X0_44,X0_45)
    | v4_pre_topc(X1_44,X0_45)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1808,plain,
    ( ~ v4_pre_topc(X0_44,sK2)
    | v4_pre_topc(k4_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2)
    | k4_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)) != X0_44 ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_2036,plain,
    ( v4_pre_topc(k4_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2)
    | ~ v4_pre_topc(k2_xboole_0(sK0(sK2),sK1(sK2)),sK2)
    | k4_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)) != k2_xboole_0(sK0(sK2),sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_5,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(sK1(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_349,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(sK1(X1),X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_350,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X1,sK2)
    | v4_pre_topc(sK1(sK2),sK2) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_568,plain,
    ( ~ v2_tex_2(X0_44,sK2)
    | ~ v2_tex_2(X1_44,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0_44,X1_44),sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0_44,sK2)
    | ~ v4_pre_topc(X1_44,sK2)
    | v4_pre_topc(sK1(sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_350])).

cnf(c_1532,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(sK1(sK2),sK2)
    | ~ v4_pre_topc(sK4,sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_6,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(sK0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_319,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(sK0(X1),X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_320,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X1,sK2)
    | v4_pre_topc(sK0(sK2),sK2) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_569,plain,
    ( ~ v2_tex_2(X0_44,sK2)
    | ~ v2_tex_2(X1_44,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0_44,X1_44),sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0_44,sK2)
    | ~ v4_pre_topc(X1_44,sK2)
    | v4_pre_topc(sK0(sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_320])).

cnf(c_1484,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(sK0(sK2),sK2)
    | ~ v4_pre_topc(sK4,sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k3_xboole_0(X2,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k3_xboole_0(X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X1,sK2)
    | v4_pre_topc(k3_xboole_0(X0,X1),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_225,plain,
    ( v4_pre_topc(k3_xboole_0(X0,X1),sK2)
    | ~ v4_pre_topc(X1,sK2)
    | ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_221,c_16])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X1,sK2)
    | v4_pre_topc(k3_xboole_0(X0,X1),sK2) ),
    inference(renaming,[status(thm)],[c_225])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0_44,sK2)
    | ~ v4_pre_topc(X1_44,sK2)
    | v4_pre_topc(k3_xboole_0(X0_44,X1_44),sK2) ),
    inference(subtyping,[status(esa)],[c_226])).

cnf(c_1369,plain,
    ( ~ m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k3_xboole_0(sK0(sK2),sK1(sK2)),sK2)
    | ~ v4_pre_topc(sK1(sK2),sK2)
    | ~ v4_pre_topc(sK0(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_1085,plain,
    ( ~ v4_pre_topc(X0_44,sK2)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2)
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)) != X0_44 ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_1282,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2)
    | ~ v4_pre_topc(k3_xboole_0(sK0(sK2),sK1(sK2)),sK2)
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)) != k3_xboole_0(sK0(sK2),sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_46))
    | k9_subset_1(X0_46,X1_44,X0_44) = k3_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1152,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X1_44,X0_44) = k3_xboole_0(X1_44,X0_44) ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_1281,plain,
    ( ~ m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)) = k3_xboole_0(sK0(sK2),sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_289,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_290,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X1,sK2) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_570,plain,
    ( ~ v2_tex_2(X0_44,sK2)
    | ~ v2_tex_2(X1_44,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0_44,X1_44),sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0_44,sK2)
    | ~ v4_pre_topc(X1_44,sK2) ),
    inference(subtyping,[status(esa)],[c_290])).

cnf(c_1245,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(sK4,sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_8,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_259,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v2_tex_2(X2,X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_260,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X1,sK2) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_571,plain,
    ( ~ v2_tex_2(X0_44,sK2)
    | ~ v2_tex_2(X1_44,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),X0_44,X1_44),sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0_44,sK2)
    | ~ v4_pre_topc(X1_44,sK2) ),
    inference(subtyping,[status(esa)],[c_260])).

cnf(c_1217,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(sK4,sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_592,plain,
    ( ~ v2_tex_2(X0_44,X0_45)
    | v2_tex_2(X1_44,X0_45)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1102,plain,
    ( ~ v2_tex_2(X0_44,sK2)
    | v2_tex_2(k4_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | k4_subset_1(u1_struct_0(sK2),sK3,sK4) != X0_44 ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_1177,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v2_tex_2(k2_xboole_0(sK3,sK4),sK2)
    | k4_subset_1(u1_struct_0(sK2),sK3,sK4) != k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_1127,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k4_subset_1(u1_struct_0(sK2),X0_44,sK4) = k2_xboole_0(X0_44,sK4) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1129,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k4_subset_1(u1_struct_0(sK2),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_584,plain,
    ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2)
    | ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK2),sK0(sK2),sK1(sK2)),sK2)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_567])).

cnf(c_9,negated_conjecture,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,negated_conjecture,
    ( v2_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_11,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,negated_conjecture,
    ( v4_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,negated_conjecture,
    ( v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2548,c_2129,c_2037,c_2036,c_1532,c_1484,c_1369,c_1282,c_1281,c_1245,c_1217,c_1177,c_1129,c_584,c_9,c_10,c_11,c_12,c_13,c_14,c_15])).


%------------------------------------------------------------------------------
