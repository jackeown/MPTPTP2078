%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:59 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 335 expanded)
%              Number of leaves         :   28 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  319 (1256 expanded)
%              Number of equality atoms :  107 ( 396 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f763,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f73,f600,f607,f649,f651,f653,f685,f687,f760,f762])).

fof(f762,plain,
    ( spl2_2
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | spl2_2
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f712,f759])).

fof(f759,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f757])).

fof(f757,plain,
    ( spl2_18
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f712,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(superposition,[],[f71,f327])).

fof(f327,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f71,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f760,plain,
    ( ~ spl2_5
    | spl2_18
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f755,f646,f757,f592])).

fof(f592,plain,
    ( spl2_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f646,plain,
    ( spl2_14
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f755,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f754,f327])).

fof(f754,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f752,f647])).

fof(f647,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f646])).

fof(f752,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f687,plain,
    ( ~ spl2_5
    | spl2_14
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f578,f65,f646,f592])).

fof(f65,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f578,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f685,plain,
    ( ~ spl2_5
    | spl2_14
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f684,f605,f69,f646,f592])).

fof(f605,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k2_xboole_0(sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f684,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f682,f619])).

fof(f619,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f617,f369])).

fof(f369,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f365,f146])).

fof(f146,plain,(
    ! [X6] : k5_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f138,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f138,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0) ),
    inference(superposition,[],[f58,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f365,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f57,f361])).

fof(f361,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f358,f314])).

fof(f314,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f134,f311])).

fof(f311,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f295,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f295,plain,(
    ! [X4] :
      ( ~ r1_tarski(k4_xboole_0(X4,X4),X4)
      | k1_xboole_0 = k4_xboole_0(X4,X4) ) ),
    inference(forward_demodulation,[],[f284,f290])).

fof(f290,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f281,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(resolution,[],[f59,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f281,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k3_xboole_0(X1,k2_xboole_0(X1,X1)) ),
    inference(superposition,[],[f202,f271])).

fof(f271,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f227,f57])).

fof(f227,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k5_xboole_0(X11,k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f135,f81])).

fof(f81,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k3_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(resolution,[],[f59,f53])).

fof(f135,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f58,f98])).

fof(f98,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f77,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f56,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f202,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f81,f98])).

fof(f284,plain,(
    ! [X4] :
      ( ~ r1_tarski(k4_xboole_0(X4,X4),k2_xboole_0(X4,X4))
      | k1_xboole_0 = k4_xboole_0(X4,X4) ) ),
    inference(superposition,[],[f60,f271])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f134,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f58,f51])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f358,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f58,f340])).

fof(f340,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f81,f336])).

fof(f336,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f327,f70])).

fof(f70,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f617,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(resolution,[],[f606,f42])).

fof(f606,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f605])).

fof(f682,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f653,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f652])).

fof(f652,plain,
    ( $false
    | spl2_13 ),
    inference(subsumption_resolution,[],[f40,f644])).

fof(f644,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f642])).

fof(f642,plain,
    ( spl2_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f651,plain,(
    spl2_12 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | spl2_12 ),
    inference(subsumption_resolution,[],[f42,f640])).

fof(f640,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl2_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f649,plain,
    ( ~ spl2_5
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | spl2_1 ),
    inference(avatar_split_clause,[],[f636,f65,f646,f642,f638,f592])).

fof(f636,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(resolution,[],[f50,f67])).

fof(f67,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f607,plain,
    ( ~ spl2_5
    | spl2_7 ),
    inference(avatar_split_clause,[],[f602,f605,f592])).

% (30008)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f602,plain,(
    ! [X0] :
      ( k2_xboole_0(sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f583,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f583,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f600,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f41,f594])).

fof(f594,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f592])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f43,f69,f65])).

fof(f43,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f44,f69,f65])).

fof(f44,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:03:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.47  % (30005)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.47  % (30007)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.50  % (30002)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.51  % (30001)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.51  % (30010)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.52  % (29996)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.52  % (30012)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.53  % (29999)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.53  % (30004)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.53  % (29997)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.53  % (29998)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.53  % (30011)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.53  % (30000)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.54  % (30012)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % (30006)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.54  % (30009)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.54  % (30003)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.54  % (30013)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f763,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(avatar_sat_refutation,[],[f72,f73,f600,f607,f649,f651,f653,f685,f687,f760,f762])).
% 0.23/0.55  fof(f762,plain,(
% 0.23/0.55    spl2_2 | ~spl2_18),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f761])).
% 0.23/0.55  fof(f761,plain,(
% 0.23/0.55    $false | (spl2_2 | ~spl2_18)),
% 0.23/0.55    inference(subsumption_resolution,[],[f712,f759])).
% 0.23/0.55  fof(f759,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_18),
% 0.23/0.55    inference(avatar_component_clause,[],[f757])).
% 0.23/0.55  fof(f757,plain,(
% 0.23/0.55    spl2_18 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.23/0.55  fof(f712,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 0.23/0.55    inference(superposition,[],[f71,f327])).
% 0.23/0.55  fof(f327,plain,(
% 0.23/0.55    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 0.23/0.55    inference(resolution,[],[f62,f42])).
% 0.23/0.55  fof(f42,plain,(
% 0.23/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 0.23/0.55  fof(f37,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f38,plain,(
% 0.23/0.55    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f36,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f35])).
% 0.23/0.55  fof(f35,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.55    inference(nnf_transformation,[],[f23])).
% 0.23/0.55  fof(f23,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f22])).
% 0.23/0.55  fof(f22,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f20])).
% 0.23/0.55  fof(f20,negated_conjecture,(
% 0.23/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.23/0.55    inference(negated_conjecture,[],[f19])).
% 0.23/0.55  fof(f19,conjecture,(
% 0.23/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.23/0.55  fof(f62,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f32])).
% 0.23/0.55  fof(f32,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f13])).
% 0.23/0.55  fof(f13,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.23/0.55  fof(f71,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 0.23/0.55    inference(avatar_component_clause,[],[f69])).
% 0.23/0.55  fof(f69,plain,(
% 0.23/0.55    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.55  fof(f760,plain,(
% 0.23/0.55    ~spl2_5 | spl2_18 | ~spl2_14),
% 0.23/0.55    inference(avatar_split_clause,[],[f755,f646,f757,f592])).
% 0.23/0.55  fof(f592,plain,(
% 0.23/0.55    spl2_5 <=> l1_pre_topc(sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.23/0.55  fof(f646,plain,(
% 0.23/0.55    spl2_14 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.23/0.55  fof(f755,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_14),
% 0.23/0.55    inference(forward_demodulation,[],[f754,f327])).
% 0.23/0.55  fof(f754,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_14),
% 0.23/0.55    inference(forward_demodulation,[],[f752,f647])).
% 0.23/0.55  fof(f647,plain,(
% 0.23/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_14),
% 0.23/0.55    inference(avatar_component_clause,[],[f646])).
% 0.23/0.55  fof(f752,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.23/0.55    inference(resolution,[],[f48,f42])).
% 0.23/0.55  fof(f48,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f25])).
% 0.23/0.55  fof(f25,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f17])).
% 0.23/0.55  fof(f17,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.23/0.55  fof(f687,plain,(
% 0.23/0.55    ~spl2_5 | spl2_14 | ~spl2_1),
% 0.23/0.55    inference(avatar_split_clause,[],[f578,f65,f646,f592])).
% 0.23/0.55  fof(f65,plain,(
% 0.23/0.55    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.55  fof(f578,plain,(
% 0.23/0.55    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.23/0.55    inference(resolution,[],[f49,f42])).
% 0.23/0.55  fof(f49,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f27])).
% 0.23/0.55  fof(f27,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f26])).
% 0.23/0.55  fof(f26,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f15])).
% 0.23/0.55  fof(f15,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.23/0.55  fof(f685,plain,(
% 0.23/0.55    ~spl2_5 | spl2_14 | ~spl2_2 | ~spl2_7),
% 0.23/0.55    inference(avatar_split_clause,[],[f684,f605,f69,f646,f592])).
% 0.23/0.55  fof(f605,plain,(
% 0.23/0.55    spl2_7 <=> ! [X0] : (k2_xboole_0(sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.23/0.55  fof(f684,plain,(
% 0.23/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_7)),
% 0.23/0.55    inference(forward_demodulation,[],[f682,f619])).
% 0.23/0.55  fof(f619,plain,(
% 0.23/0.55    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_7)),
% 0.23/0.55    inference(forward_demodulation,[],[f617,f369])).
% 0.23/0.55  fof(f369,plain,(
% 0.23/0.55    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.23/0.55    inference(forward_demodulation,[],[f365,f146])).
% 0.23/0.55  fof(f146,plain,(
% 0.23/0.55    ( ! [X6] : (k5_xboole_0(X6,k1_xboole_0) = X6) )),
% 0.23/0.55    inference(forward_demodulation,[],[f138,f46])).
% 0.23/0.55  fof(f46,plain,(
% 0.23/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f7])).
% 0.23/0.55  fof(f7,axiom,(
% 0.23/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.55  fof(f138,plain,(
% 0.23/0.55    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)) )),
% 0.23/0.55    inference(superposition,[],[f58,f45])).
% 0.23/0.55  fof(f45,plain,(
% 0.23/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f4])).
% 0.23/0.55  fof(f4,axiom,(
% 0.23/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.23/0.55  fof(f58,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f2])).
% 0.23/0.55  fof(f2,axiom,(
% 0.23/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.55  fof(f365,plain,(
% 0.23/0.55    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl2_2),
% 0.23/0.55    inference(superposition,[],[f57,f361])).
% 0.23/0.55  fof(f361,plain,(
% 0.23/0.55    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 0.23/0.55    inference(forward_demodulation,[],[f358,f314])).
% 0.23/0.55  fof(f314,plain,(
% 0.23/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.23/0.55    inference(backward_demodulation,[],[f134,f311])).
% 0.23/0.55  fof(f311,plain,(
% 0.23/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.23/0.55    inference(resolution,[],[f295,f53])).
% 0.23/0.55  fof(f53,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f5])).
% 0.23/0.55  fof(f5,axiom,(
% 0.23/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.23/0.55  fof(f295,plain,(
% 0.23/0.55    ( ! [X4] : (~r1_tarski(k4_xboole_0(X4,X4),X4) | k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 0.23/0.55    inference(forward_demodulation,[],[f284,f290])).
% 0.23/0.55  fof(f290,plain,(
% 0.23/0.55    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 0.23/0.55    inference(forward_demodulation,[],[f281,f79])).
% 0.23/0.55  fof(f79,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.23/0.55    inference(resolution,[],[f59,f52])).
% 0.23/0.55  fof(f52,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f8])).
% 0.23/0.55  fof(f8,axiom,(
% 0.23/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.23/0.55  fof(f59,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f28])).
% 0.23/0.55  fof(f28,plain,(
% 0.23/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f3])).
% 0.23/0.55  fof(f3,axiom,(
% 0.23/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.55  fof(f281,plain,(
% 0.23/0.55    ( ! [X1] : (k2_xboole_0(X1,X1) = k3_xboole_0(X1,k2_xboole_0(X1,X1))) )),
% 0.23/0.55    inference(superposition,[],[f202,f271])).
% 0.23/0.55  fof(f271,plain,(
% 0.23/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 0.23/0.55    inference(superposition,[],[f227,f57])).
% 0.23/0.55  fof(f227,plain,(
% 0.23/0.55    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k5_xboole_0(X11,k4_xboole_0(X11,X12))) )),
% 0.23/0.55    inference(superposition,[],[f135,f81])).
% 0.23/0.55  fof(f81,plain,(
% 0.23/0.55    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k3_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 0.23/0.55    inference(resolution,[],[f59,f53])).
% 0.23/0.55  fof(f135,plain,(
% 0.23/0.55    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 0.23/0.55    inference(superposition,[],[f58,f98])).
% 0.23/0.55  fof(f98,plain,(
% 0.23/0.55    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.23/0.55    inference(superposition,[],[f77,f56])).
% 0.23/0.55  fof(f56,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f14])).
% 0.23/0.55  fof(f14,axiom,(
% 0.23/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.55  fof(f77,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.23/0.55    inference(superposition,[],[f56,f54])).
% 0.23/0.55  fof(f54,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f10])).
% 0.23/0.55  fof(f10,axiom,(
% 0.23/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.55  fof(f202,plain,(
% 0.23/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 0.23/0.55    inference(superposition,[],[f81,f98])).
% 0.23/0.55  fof(f284,plain,(
% 0.23/0.55    ( ! [X4] : (~r1_tarski(k4_xboole_0(X4,X4),k2_xboole_0(X4,X4)) | k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 0.23/0.55    inference(superposition,[],[f60,f271])).
% 0.23/0.55  fof(f60,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f29])).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f6])).
% 0.23/0.55  fof(f6,axiom,(
% 0.23/0.55    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.23/0.55  fof(f134,plain,(
% 0.23/0.55    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.23/0.55    inference(superposition,[],[f58,f51])).
% 0.23/0.55  fof(f51,plain,(
% 0.23/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f21])).
% 0.23/0.55  fof(f21,plain,(
% 0.23/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.23/0.55    inference(rectify,[],[f1])).
% 0.23/0.55  fof(f1,axiom,(
% 0.23/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.23/0.55  fof(f358,plain,(
% 0.23/0.55    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.23/0.55    inference(superposition,[],[f58,f340])).
% 0.23/0.55  fof(f340,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 0.23/0.55    inference(superposition,[],[f81,f336])).
% 0.23/0.55  fof(f336,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.23/0.55    inference(superposition,[],[f327,f70])).
% 0.23/0.55  fof(f70,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.23/0.55    inference(avatar_component_clause,[],[f69])).
% 0.23/0.55  fof(f57,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f9])).
% 0.23/0.55  fof(f9,axiom,(
% 0.23/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.23/0.55  fof(f617,plain,(
% 0.23/0.55    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_7),
% 0.23/0.55    inference(resolution,[],[f606,f42])).
% 0.23/0.55  fof(f606,plain,(
% 0.23/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))) ) | ~spl2_7),
% 0.23/0.55    inference(avatar_component_clause,[],[f605])).
% 0.23/0.55  fof(f682,plain,(
% 0.23/0.55    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.23/0.55    inference(resolution,[],[f47,f42])).
% 0.23/0.55  fof(f47,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f24])).
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f18])).
% 0.23/0.55  fof(f18,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.23/0.55  fof(f653,plain,(
% 0.23/0.55    spl2_13),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f652])).
% 0.23/0.55  fof(f652,plain,(
% 0.23/0.55    $false | spl2_13),
% 0.23/0.55    inference(subsumption_resolution,[],[f40,f644])).
% 0.23/0.55  fof(f644,plain,(
% 0.23/0.55    ~v2_pre_topc(sK0) | spl2_13),
% 0.23/0.55    inference(avatar_component_clause,[],[f642])).
% 0.23/0.55  fof(f642,plain,(
% 0.23/0.55    spl2_13 <=> v2_pre_topc(sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.23/0.55  fof(f40,plain,(
% 0.23/0.55    v2_pre_topc(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f651,plain,(
% 0.23/0.55    spl2_12),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f650])).
% 0.23/0.55  fof(f650,plain,(
% 0.23/0.55    $false | spl2_12),
% 0.23/0.55    inference(subsumption_resolution,[],[f42,f640])).
% 0.23/0.55  fof(f640,plain,(
% 0.23/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_12),
% 0.23/0.55    inference(avatar_component_clause,[],[f638])).
% 0.23/0.55  fof(f638,plain,(
% 0.23/0.55    spl2_12 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.23/0.55  fof(f649,plain,(
% 0.23/0.55    ~spl2_5 | ~spl2_12 | ~spl2_13 | ~spl2_14 | spl2_1),
% 0.23/0.55    inference(avatar_split_clause,[],[f636,f65,f646,f642,f638,f592])).
% 0.23/0.55  fof(f636,plain,(
% 0.23/0.55    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_1),
% 0.23/0.55    inference(resolution,[],[f50,f67])).
% 0.23/0.55  fof(f67,plain,(
% 0.23/0.55    ~v4_pre_topc(sK1,sK0) | spl2_1),
% 0.23/0.55    inference(avatar_component_clause,[],[f65])).
% 0.23/0.55  fof(f50,plain,(
% 0.23/0.55    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f27])).
% 0.23/0.55  fof(f607,plain,(
% 0.23/0.55    ~spl2_5 | spl2_7),
% 0.23/0.55    inference(avatar_split_clause,[],[f602,f605,f592])).
% 0.23/0.55  % (30008)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.55  fof(f602,plain,(
% 0.23/0.55    ( ! [X0] : (k2_xboole_0(sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.23/0.55    inference(resolution,[],[f583,f61])).
% 0.23/0.55  fof(f61,plain,(
% 0.23/0.55    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f31])).
% 0.23/0.55  fof(f31,plain,(
% 0.23/0.55    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f30])).
% 0.23/0.55  fof(f30,plain,(
% 0.23/0.55    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f16])).
% 0.23/0.55  fof(f16,axiom,(
% 0.23/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.23/0.55  fof(f583,plain,(
% 0.23/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)) )),
% 0.23/0.55    inference(resolution,[],[f63,f42])).
% 0.23/0.55  fof(f63,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f34])).
% 0.23/0.55  fof(f34,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.55    inference(flattening,[],[f33])).
% 0.23/0.55  fof(f33,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.23/0.55    inference(ennf_transformation,[],[f12])).
% 0.23/0.55  fof(f12,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.23/0.55  fof(f600,plain,(
% 0.23/0.55    spl2_5),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f599])).
% 0.23/0.55  fof(f599,plain,(
% 0.23/0.55    $false | spl2_5),
% 0.23/0.55    inference(subsumption_resolution,[],[f41,f594])).
% 0.23/0.55  fof(f594,plain,(
% 0.23/0.55    ~l1_pre_topc(sK0) | spl2_5),
% 0.23/0.55    inference(avatar_component_clause,[],[f592])).
% 0.23/0.55  fof(f41,plain,(
% 0.23/0.55    l1_pre_topc(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f73,plain,(
% 0.23/0.55    spl2_1 | spl2_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f43,f69,f65])).
% 0.23/0.55  fof(f43,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f72,plain,(
% 0.23/0.55    ~spl2_1 | ~spl2_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f44,f69,f65])).
% 0.23/0.55  fof(f44,plain,(
% 0.23/0.55    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  % SZS output end Proof for theBenchmark
% 0.23/0.55  % (30012)------------------------------
% 0.23/0.55  % (30012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (30012)Termination reason: Refutation
% 0.23/0.55  
% 0.23/0.55  % (30012)Memory used [KB]: 6524
% 0.23/0.55  % (30012)Time elapsed: 0.098 s
% 0.23/0.55  % (30012)------------------------------
% 0.23/0.55  % (30012)------------------------------
% 0.23/0.55  % (29995)Success in time 0.188 s
%------------------------------------------------------------------------------
