%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:39 EST 2020

% Result     : Theorem 2.78s
% Output     : Refutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 520 expanded)
%              Number of leaves         :   20 ( 145 expanded)
%              Depth                    :   19
%              Number of atoms          :  344 (2601 expanded)
%              Number of equality atoms :   68 ( 674 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1616,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f94,f598,f1506,f1556,f1560,f1615])).

fof(f1615,plain,
    ( spl2_2
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f1614])).

fof(f1614,plain,
    ( $false
    | spl2_2
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1613,f61])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f1613,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1612,f62])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f1612,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1607,f92])).

fof(f92,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1607,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_28 ),
    inference(superposition,[],[f67,f596])).

fof(f596,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl2_28
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1560,plain,
    ( ~ spl2_1
    | spl2_27 ),
    inference(avatar_split_clause,[],[f1559,f590,f86])).

fof(f86,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f590,plain,
    ( spl2_27
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f1559,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_27 ),
    inference(subsumption_resolution,[],[f1558,f61])).

fof(f1558,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(subsumption_resolution,[],[f1557,f62])).

fof(f1557,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(subsumption_resolution,[],[f624,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f624,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(duplicate_literal_removal,[],[f621])).

fof(f621,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(resolution,[],[f592,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f592,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f590])).

fof(f1556,plain,
    ( spl2_1
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f1555])).

fof(f1555,plain,
    ( $false
    | spl2_1
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1554,f60])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f1554,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_1
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1553,f61])).

fof(f1553,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl2_1
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1552,f62])).

fof(f1552,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl2_1
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1538,f88])).

fof(f88,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f1538,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_28 ),
    inference(superposition,[],[f72,f596])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f1506,plain,
    ( spl2_28
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f1505,f90,f594])).

fof(f1505,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1504,f274])).

fof(f274,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f270,f273])).

fof(f273,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f269,f144])).

fof(f144,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f142,f117])).

fof(f117,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f104,f61])).

fof(f104,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f142,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f91,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f91,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f269,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f149,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f149,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f119,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f119,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f106,f61])).

fof(f106,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f270,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(resolution,[],[f149,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1504,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1500,f1503])).

fof(f1503,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1499,f346])).

fof(f346,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f344,f117])).

fof(f344,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f118,f65])).

fof(f118,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f105,f61])).

fof(f105,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f67])).

fof(f1499,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f759,f81])).

fof(f759,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f569,f76])).

fof(f569,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f433,f267])).

fof(f267,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f266,f61])).

fof(f266,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f264,f62])).

fof(f264,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f116,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f116,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) ),
    inference(resolution,[],[f62,f65])).

fof(f433,plain,(
    ! [X3] : r1_tarski(k4_xboole_0(sK1,X3),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f151,f73])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f151,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(X1,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f119,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1500,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f759,f80])).

fof(f598,plain,
    ( ~ spl2_27
    | spl2_28 ),
    inference(avatar_split_clause,[],[f584,f594,f590])).

fof(f584,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f572,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f572,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f73,f267])).

fof(f94,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f63,f90,f86])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f64,f90,f86])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:37:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (21638)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (21637)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (21646)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.57  % (21647)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.57/0.57  % (21655)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.57  % (21654)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.57/0.58  % (21639)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.59  % (21645)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.76/0.59  % (21653)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.76/0.60  % (21661)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.76/0.60  % (21634)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.76/0.60  % (21659)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.76/0.60  % (21635)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.76/0.61  % (21636)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.76/0.61  % (21652)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.76/0.61  % (21658)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.76/0.61  % (21633)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.76/0.62  % (21642)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.76/0.62  % (21651)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.76/0.62  % (21632)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.76/0.62  % (21650)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.76/0.62  % (21644)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.76/0.62  % (21640)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.76/0.62  % (21643)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.76/0.63  % (21660)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.76/0.63  % (21649)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.76/0.64  % (21657)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.76/0.65  % (21648)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.76/0.66  % (21641)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.76/0.66  % (21656)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.78/0.77  % (21644)Refutation found. Thanks to Tanya!
% 2.78/0.77  % SZS status Theorem for theBenchmark
% 2.78/0.77  % SZS output start Proof for theBenchmark
% 2.78/0.77  fof(f1616,plain,(
% 2.78/0.77    $false),
% 2.78/0.77    inference(avatar_sat_refutation,[],[f93,f94,f598,f1506,f1556,f1560,f1615])).
% 2.78/0.77  fof(f1615,plain,(
% 2.78/0.77    spl2_2 | ~spl2_28),
% 2.78/0.77    inference(avatar_contradiction_clause,[],[f1614])).
% 2.78/0.77  fof(f1614,plain,(
% 2.78/0.77    $false | (spl2_2 | ~spl2_28)),
% 2.78/0.77    inference(subsumption_resolution,[],[f1613,f61])).
% 2.78/0.77  fof(f61,plain,(
% 2.78/0.77    l1_pre_topc(sK0)),
% 2.78/0.77    inference(cnf_transformation,[],[f56])).
% 2.78/0.77  fof(f56,plain,(
% 2.78/0.77    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.78/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).
% 2.78/0.77  fof(f54,plain,(
% 2.78/0.77    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.78/0.77    introduced(choice_axiom,[])).
% 2.78/0.77  fof(f55,plain,(
% 2.78/0.77    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.78/0.77    introduced(choice_axiom,[])).
% 2.78/0.77  fof(f53,plain,(
% 2.78/0.77    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.78/0.77    inference(flattening,[],[f52])).
% 2.78/0.77  fof(f52,plain,(
% 2.78/0.77    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.78/0.77    inference(nnf_transformation,[],[f35])).
% 2.78/0.77  fof(f35,plain,(
% 2.78/0.77    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.78/0.77    inference(flattening,[],[f34])).
% 2.78/0.77  fof(f34,plain,(
% 2.78/0.77    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.78/0.77    inference(ennf_transformation,[],[f33])).
% 2.78/0.77  fof(f33,negated_conjecture,(
% 2.78/0.77    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.78/0.77    inference(negated_conjecture,[],[f32])).
% 2.78/0.77  fof(f32,conjecture,(
% 2.78/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.78/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.78/0.78  fof(f1613,plain,(
% 2.78/0.78    ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_28)),
% 2.78/0.78    inference(subsumption_resolution,[],[f1612,f62])).
% 2.78/0.78  fof(f62,plain,(
% 2.78/0.78    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.78/0.78    inference(cnf_transformation,[],[f56])).
% 2.78/0.78  fof(f1612,plain,(
% 2.78/0.78    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_28)),
% 2.78/0.78    inference(subsumption_resolution,[],[f1607,f92])).
% 2.78/0.78  fof(f92,plain,(
% 2.78/0.78    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 2.78/0.78    inference(avatar_component_clause,[],[f90])).
% 2.78/0.78  fof(f90,plain,(
% 2.78/0.78    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.78/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.78/0.78  fof(f1607,plain,(
% 2.78/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_28),
% 2.78/0.78    inference(superposition,[],[f67,f596])).
% 2.78/0.78  fof(f596,plain,(
% 2.78/0.78    sK1 = k1_tops_1(sK0,sK1) | ~spl2_28),
% 2.78/0.78    inference(avatar_component_clause,[],[f594])).
% 2.78/0.78  fof(f594,plain,(
% 2.78/0.78    spl2_28 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.78/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 2.78/0.78  fof(f67,plain,(
% 2.78/0.78    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.78/0.78    inference(cnf_transformation,[],[f39])).
% 2.78/0.78  fof(f39,plain,(
% 2.78/0.78    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.78    inference(ennf_transformation,[],[f28])).
% 2.78/0.78  fof(f28,axiom,(
% 2.78/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.78/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.78/0.78  fof(f1560,plain,(
% 2.78/0.78    ~spl2_1 | spl2_27),
% 2.78/0.78    inference(avatar_split_clause,[],[f1559,f590,f86])).
% 2.78/0.78  fof(f86,plain,(
% 2.78/0.78    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 2.78/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.78/0.78  fof(f590,plain,(
% 2.78/0.78    spl2_27 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.78/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 2.78/0.78  fof(f1559,plain,(
% 2.78/0.78    ~v3_pre_topc(sK1,sK0) | spl2_27),
% 2.78/0.78    inference(subsumption_resolution,[],[f1558,f61])).
% 2.78/0.78  fof(f1558,plain,(
% 2.78/0.78    ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl2_27),
% 2.78/0.78    inference(subsumption_resolution,[],[f1557,f62])).
% 2.78/0.78  fof(f1557,plain,(
% 2.78/0.78    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_27),
% 2.78/0.78    inference(subsumption_resolution,[],[f624,f84])).
% 2.78/0.78  fof(f84,plain,(
% 2.78/0.78    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.78/0.78    inference(equality_resolution,[],[f77])).
% 2.78/0.78  fof(f77,plain,(
% 2.78/0.78    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.78/0.78    inference(cnf_transformation,[],[f59])).
% 2.78/0.78  fof(f59,plain,(
% 2.78/0.78    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/0.78    inference(flattening,[],[f58])).
% 2.78/0.78  fof(f58,plain,(
% 2.78/0.78    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/0.78    inference(nnf_transformation,[],[f3])).
% 2.78/0.78  fof(f3,axiom,(
% 2.78/0.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.78/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.78/0.78  fof(f624,plain,(
% 2.78/0.78    ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_27),
% 2.78/0.78    inference(duplicate_literal_removal,[],[f621])).
% 2.78/0.79  fof(f621,plain,(
% 2.78/0.79    ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_27),
% 2.78/0.79    inference(resolution,[],[f592,f71])).
% 2.78/0.79  fof(f71,plain,(
% 2.78/0.79    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.78/0.79    inference(cnf_transformation,[],[f44])).
% 2.78/0.79  fof(f44,plain,(
% 2.78/0.79    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.79    inference(flattening,[],[f43])).
% 2.78/0.79  fof(f43,plain,(
% 2.78/0.79    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.79    inference(ennf_transformation,[],[f29])).
% 2.78/0.79  fof(f29,axiom,(
% 2.78/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 2.78/0.79  fof(f592,plain,(
% 2.78/0.79    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl2_27),
% 2.78/0.79    inference(avatar_component_clause,[],[f590])).
% 2.78/0.79  fof(f1556,plain,(
% 2.78/0.79    spl2_1 | ~spl2_28),
% 2.78/0.79    inference(avatar_contradiction_clause,[],[f1555])).
% 2.78/0.79  fof(f1555,plain,(
% 2.78/0.79    $false | (spl2_1 | ~spl2_28)),
% 2.78/0.79    inference(subsumption_resolution,[],[f1554,f60])).
% 2.78/0.79  fof(f60,plain,(
% 2.78/0.79    v2_pre_topc(sK0)),
% 2.78/0.79    inference(cnf_transformation,[],[f56])).
% 2.78/0.79  fof(f1554,plain,(
% 2.78/0.79    ~v2_pre_topc(sK0) | (spl2_1 | ~spl2_28)),
% 2.78/0.79    inference(subsumption_resolution,[],[f1553,f61])).
% 2.78/0.79  fof(f1553,plain,(
% 2.78/0.79    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl2_1 | ~spl2_28)),
% 2.78/0.79    inference(subsumption_resolution,[],[f1552,f62])).
% 2.78/0.79  fof(f1552,plain,(
% 2.78/0.79    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl2_1 | ~spl2_28)),
% 2.78/0.79    inference(subsumption_resolution,[],[f1538,f88])).
% 2.78/0.79  fof(f88,plain,(
% 2.78/0.79    ~v3_pre_topc(sK1,sK0) | spl2_1),
% 2.78/0.79    inference(avatar_component_clause,[],[f86])).
% 2.78/0.79  fof(f1538,plain,(
% 2.78/0.79    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_28),
% 2.78/0.79    inference(superposition,[],[f72,f596])).
% 2.78/0.79  fof(f72,plain,(
% 2.78/0.79    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.78/0.79    inference(cnf_transformation,[],[f46])).
% 2.78/0.79  fof(f46,plain,(
% 2.78/0.79    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.79    inference(flattening,[],[f45])).
% 2.78/0.79  fof(f45,plain,(
% 2.78/0.79    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.78/0.79    inference(ennf_transformation,[],[f27])).
% 2.78/0.79  fof(f27,axiom,(
% 2.78/0.79    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.78/0.79  fof(f1506,plain,(
% 2.78/0.79    spl2_28 | ~spl2_2),
% 2.78/0.79    inference(avatar_split_clause,[],[f1505,f90,f594])).
% 2.78/0.79  fof(f1505,plain,(
% 2.78/0.79    sK1 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 2.78/0.79    inference(forward_demodulation,[],[f1504,f274])).
% 2.78/0.79  fof(f274,plain,(
% 2.78/0.79    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_2),
% 2.78/0.79    inference(forward_demodulation,[],[f270,f273])).
% 2.78/0.79  fof(f273,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.78/0.79    inference(forward_demodulation,[],[f269,f144])).
% 2.78/0.79  fof(f144,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.78/0.79    inference(subsumption_resolution,[],[f142,f117])).
% 2.78/0.79  fof(f117,plain,(
% 2.78/0.79    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.78/0.79    inference(subsumption_resolution,[],[f104,f61])).
% 2.78/0.79  fof(f104,plain,(
% 2.78/0.79    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.78/0.79    inference(resolution,[],[f62,f66])).
% 2.78/0.79  fof(f66,plain,(
% 2.78/0.79    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.78/0.79    inference(cnf_transformation,[],[f38])).
% 2.78/0.79  fof(f38,plain,(
% 2.78/0.79    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.78/0.79    inference(flattening,[],[f37])).
% 2.78/0.79  fof(f37,plain,(
% 2.78/0.79    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.78/0.79    inference(ennf_transformation,[],[f25])).
% 2.78/0.79  fof(f25,axiom,(
% 2.78/0.79    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.78/0.79  fof(f142,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 2.78/0.79    inference(superposition,[],[f91,f65])).
% 2.78/0.79  fof(f65,plain,(
% 2.78/0.79    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.78/0.79    inference(cnf_transformation,[],[f36])).
% 2.78/0.79  fof(f36,plain,(
% 2.78/0.79    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.78/0.79    inference(ennf_transformation,[],[f19])).
% 2.78/0.79  fof(f19,axiom,(
% 2.78/0.79    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.78/0.79  fof(f91,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.78/0.79    inference(avatar_component_clause,[],[f90])).
% 2.78/0.79  fof(f269,plain,(
% 2.78/0.79    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 2.78/0.79    inference(resolution,[],[f149,f81])).
% 2.78/0.79  fof(f81,plain,(
% 2.78/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.78/0.79    inference(cnf_transformation,[],[f50])).
% 2.78/0.79  fof(f50,plain,(
% 2.78/0.79    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.78/0.79    inference(ennf_transformation,[],[f15])).
% 2.78/0.79  fof(f15,axiom,(
% 2.78/0.79    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.78/0.79  fof(f149,plain,(
% 2.78/0.79    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.78/0.79    inference(resolution,[],[f119,f76])).
% 2.78/0.79  fof(f76,plain,(
% 2.78/0.79    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.78/0.79    inference(cnf_transformation,[],[f57])).
% 2.78/0.79  fof(f57,plain,(
% 2.78/0.79    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.78/0.79    inference(nnf_transformation,[],[f23])).
% 2.78/0.79  fof(f23,axiom,(
% 2.78/0.79    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.78/0.79  fof(f119,plain,(
% 2.78/0.79    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.78/0.79    inference(subsumption_resolution,[],[f106,f61])).
% 2.78/0.79  fof(f106,plain,(
% 2.78/0.79    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.78/0.79    inference(resolution,[],[f62,f68])).
% 2.78/0.79  fof(f68,plain,(
% 2.78/0.79    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.78/0.79    inference(cnf_transformation,[],[f40])).
% 2.78/0.79  fof(f40,plain,(
% 2.78/0.79    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.79    inference(ennf_transformation,[],[f26])).
% 2.78/0.79  fof(f26,axiom,(
% 2.78/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.78/0.79  fof(f270,plain,(
% 2.78/0.79    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 2.78/0.79    inference(resolution,[],[f149,f80])).
% 2.78/0.79  fof(f80,plain,(
% 2.78/0.79    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.78/0.79    inference(cnf_transformation,[],[f49])).
% 2.78/0.79  fof(f49,plain,(
% 2.78/0.79    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.78/0.79    inference(ennf_transformation,[],[f18])).
% 2.78/0.79  fof(f18,axiom,(
% 2.78/0.79    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.78/0.79  fof(f1504,plain,(
% 2.78/0.79    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.78/0.79    inference(forward_demodulation,[],[f1500,f1503])).
% 2.78/0.79  fof(f1503,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.78/0.79    inference(forward_demodulation,[],[f1499,f346])).
% 2.78/0.79  fof(f346,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.78/0.79    inference(subsumption_resolution,[],[f344,f117])).
% 2.78/0.79  fof(f344,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.78/0.79    inference(superposition,[],[f118,f65])).
% 2.78/0.79  fof(f118,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.78/0.79    inference(subsumption_resolution,[],[f105,f61])).
% 2.78/0.79  fof(f105,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.78/0.79    inference(resolution,[],[f62,f67])).
% 2.78/0.79  fof(f1499,plain,(
% 2.78/0.79    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.78/0.79    inference(resolution,[],[f759,f81])).
% 2.78/0.79  fof(f759,plain,(
% 2.78/0.79    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.78/0.79    inference(resolution,[],[f569,f76])).
% 2.78/0.79  fof(f569,plain,(
% 2.78/0.79    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 2.78/0.79    inference(superposition,[],[f433,f267])).
% 2.78/0.79  fof(f267,plain,(
% 2.78/0.79    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.78/0.79    inference(subsumption_resolution,[],[f266,f61])).
% 2.78/0.79  fof(f266,plain,(
% 2.78/0.79    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.78/0.79    inference(subsumption_resolution,[],[f264,f62])).
% 2.78/0.79  fof(f264,plain,(
% 2.78/0.79    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.78/0.79    inference(superposition,[],[f116,f69])).
% 2.78/0.79  fof(f69,plain,(
% 2.78/0.79    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.78/0.79    inference(cnf_transformation,[],[f41])).
% 2.78/0.79  fof(f41,plain,(
% 2.78/0.79    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.79    inference(ennf_transformation,[],[f31])).
% 2.78/0.79  fof(f31,axiom,(
% 2.78/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.78/0.79  fof(f116,plain,(
% 2.78/0.79    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)) )),
% 2.78/0.79    inference(resolution,[],[f62,f65])).
% 2.78/0.79  fof(f433,plain,(
% 2.78/0.79    ( ! [X3] : (r1_tarski(k4_xboole_0(sK1,X3),k2_pre_topc(sK0,sK1))) )),
% 2.78/0.79    inference(resolution,[],[f151,f73])).
% 2.78/0.79  fof(f73,plain,(
% 2.78/0.79    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.78/0.79    inference(cnf_transformation,[],[f9])).
% 2.78/0.79  fof(f9,axiom,(
% 2.78/0.79    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.78/0.79  fof(f151,plain,(
% 2.78/0.79    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(X1,k2_pre_topc(sK0,sK1))) )),
% 2.78/0.79    inference(resolution,[],[f119,f74])).
% 2.78/0.79  fof(f74,plain,(
% 2.78/0.79    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.78/0.79    inference(cnf_transformation,[],[f48])).
% 2.78/0.79  fof(f48,plain,(
% 2.78/0.79    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.78/0.79    inference(flattening,[],[f47])).
% 2.78/0.79  fof(f47,plain,(
% 2.78/0.79    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.78/0.79    inference(ennf_transformation,[],[f7])).
% 2.78/0.79  fof(f7,axiom,(
% 2.78/0.79    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.78/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.78/0.79  fof(f1500,plain,(
% 2.78/0.79    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 2.78/0.79    inference(resolution,[],[f759,f80])).
% 2.78/0.79  fof(f598,plain,(
% 2.78/0.79    ~spl2_27 | spl2_28),
% 2.78/0.79    inference(avatar_split_clause,[],[f584,f594,f590])).
% 2.78/0.79  fof(f584,plain,(
% 2.78/0.79    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.78/0.79    inference(resolution,[],[f572,f79])).
% 2.78/0.79  fof(f79,plain,(
% 2.78/0.79    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.78/0.79    inference(cnf_transformation,[],[f59])).
% 2.78/0.79  fof(f572,plain,(
% 2.78/0.79    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.78/0.79    inference(superposition,[],[f73,f267])).
% 2.78/0.79  fof(f94,plain,(
% 2.78/0.79    spl2_1 | spl2_2),
% 2.78/0.79    inference(avatar_split_clause,[],[f63,f90,f86])).
% 2.78/0.79  fof(f63,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.78/0.79    inference(cnf_transformation,[],[f56])).
% 2.78/0.79  fof(f93,plain,(
% 2.78/0.79    ~spl2_1 | ~spl2_2),
% 2.78/0.79    inference(avatar_split_clause,[],[f64,f90,f86])).
% 2.78/0.79  fof(f64,plain,(
% 2.78/0.79    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.78/0.79    inference(cnf_transformation,[],[f56])).
% 2.78/0.79  % SZS output end Proof for theBenchmark
% 2.78/0.79  % (21644)------------------------------
% 2.78/0.79  % (21644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.79  % (21644)Termination reason: Refutation
% 2.78/0.79  
% 2.78/0.79  % (21644)Memory used [KB]: 11385
% 2.78/0.79  % (21644)Time elapsed: 0.341 s
% 2.78/0.79  % (21644)------------------------------
% 2.78/0.79  % (21644)------------------------------
% 2.78/0.79  % (21631)Success in time 0.422 s
%------------------------------------------------------------------------------
