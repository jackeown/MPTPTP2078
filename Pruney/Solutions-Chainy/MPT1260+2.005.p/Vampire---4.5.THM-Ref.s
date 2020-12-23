%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:33 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
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
fof(f1614,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f92,f596,f1504,f1554,f1558,f1613])).

fof(f1613,plain,
    ( spl2_2
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f1612])).

fof(f1612,plain,
    ( $false
    | spl2_2
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1611,f59])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f52,plain,
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

fof(f53,plain,
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

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f1611,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1610,f60])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f1610,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1605,f90])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1605,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_28 ),
    inference(superposition,[],[f65,f594])).

fof(f594,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl2_28
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1558,plain,
    ( ~ spl2_1
    | spl2_27 ),
    inference(avatar_split_clause,[],[f1557,f588,f84])).

fof(f84,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f588,plain,
    ( spl2_27
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f1557,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_27 ),
    inference(subsumption_resolution,[],[f1556,f59])).

fof(f1556,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(subsumption_resolution,[],[f1555,f60])).

fof(f1555,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(subsumption_resolution,[],[f622,f82])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f622,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(duplicate_literal_removal,[],[f619])).

fof(f619,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(resolution,[],[f590,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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

fof(f590,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f588])).

fof(f1554,plain,
    ( spl2_1
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f1553])).

fof(f1553,plain,
    ( $false
    | spl2_1
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1552,f58])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f1552,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_1
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1551,f59])).

fof(f1551,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl2_1
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1550,f60])).

fof(f1550,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl2_1
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1536,f86])).

fof(f86,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1536,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_28 ),
    inference(superposition,[],[f70,f594])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f1504,plain,
    ( spl2_28
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f1503,f88,f592])).

fof(f1503,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1502,f272])).

fof(f272,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f268,f271])).

fof(f271,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f267,f142])).

fof(f142,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f140,f115])).

fof(f115,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f102,f59])).

fof(f102,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f140,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f89,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f89,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f267,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f147,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f147,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f117,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f117,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f104,f59])).

fof(f104,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f268,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(resolution,[],[f147,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1502,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1498,f1501])).

fof(f1501,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1497,f344])).

fof(f344,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f342,f115])).

fof(f342,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f116,f63])).

fof(f116,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f103,f59])).

fof(f103,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f65])).

fof(f1497,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f757,f79])).

fof(f757,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f567,f74])).

fof(f567,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f431,f265])).

fof(f265,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f264,f59])).

fof(f264,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f262,f60])).

fof(f262,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f114,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f114,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) ),
    inference(resolution,[],[f60,f63])).

fof(f431,plain,(
    ! [X3] : r1_tarski(k4_xboole_0(sK1,X3),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f149,f71])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f149,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(X1,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f117,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1498,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f757,f78])).

fof(f596,plain,
    ( ~ spl2_27
    | spl2_28 ),
    inference(avatar_split_clause,[],[f582,f592,f588])).

fof(f582,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f570,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f570,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f71,f265])).

fof(f92,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f61,f88,f84])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f62,f88,f84])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (6509)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.50  % (6501)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (6516)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.50  % (6491)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (6518)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (6497)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (6508)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (6495)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (6494)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (6521)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (6513)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (6492)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (6515)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (6512)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (6507)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (6505)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (6519)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (6500)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (6502)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (6499)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (6498)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (6511)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (6493)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (6514)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (6520)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (6503)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (6504)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (6517)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (6506)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (6510)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.13/0.63  % (6504)Refutation found. Thanks to Tanya!
% 2.13/0.63  % SZS status Theorem for theBenchmark
% 2.13/0.63  % SZS output start Proof for theBenchmark
% 2.13/0.63  fof(f1614,plain,(
% 2.13/0.63    $false),
% 2.13/0.63    inference(avatar_sat_refutation,[],[f91,f92,f596,f1504,f1554,f1558,f1613])).
% 2.13/0.63  fof(f1613,plain,(
% 2.13/0.63    spl2_2 | ~spl2_28),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f1612])).
% 2.13/0.63  fof(f1612,plain,(
% 2.13/0.63    $false | (spl2_2 | ~spl2_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1611,f59])).
% 2.13/0.63  fof(f59,plain,(
% 2.13/0.63    l1_pre_topc(sK0)),
% 2.13/0.63    inference(cnf_transformation,[],[f54])).
% 2.13/0.63  fof(f54,plain,(
% 2.13/0.63    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.13/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).
% 2.13/0.63  fof(f52,plain,(
% 2.13/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.13/0.63    introduced(choice_axiom,[])).
% 2.13/0.63  fof(f53,plain,(
% 2.13/0.63    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.63    introduced(choice_axiom,[])).
% 2.13/0.63  fof(f51,plain,(
% 2.13/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.13/0.63    inference(flattening,[],[f50])).
% 2.13/0.63  fof(f50,plain,(
% 2.13/0.63    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.13/0.63    inference(nnf_transformation,[],[f33])).
% 2.13/0.63  fof(f33,plain,(
% 2.13/0.63    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.13/0.63    inference(flattening,[],[f32])).
% 2.13/0.63  fof(f32,plain,(
% 2.13/0.63    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f31])).
% 2.13/0.63  fof(f31,negated_conjecture,(
% 2.13/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.13/0.63    inference(negated_conjecture,[],[f30])).
% 2.13/0.63  fof(f30,conjecture,(
% 2.13/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.13/0.63  fof(f1611,plain,(
% 2.13/0.63    ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1610,f60])).
% 2.13/0.63  fof(f60,plain,(
% 2.13/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.63    inference(cnf_transformation,[],[f54])).
% 2.13/0.63  fof(f1610,plain,(
% 2.13/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1605,f90])).
% 2.13/0.63  fof(f90,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 2.13/0.63    inference(avatar_component_clause,[],[f88])).
% 2.13/0.63  fof(f88,plain,(
% 2.13/0.63    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.13/0.63  fof(f1605,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_28),
% 2.13/0.63    inference(superposition,[],[f65,f594])).
% 2.13/0.63  fof(f594,plain,(
% 2.13/0.63    sK1 = k1_tops_1(sK0,sK1) | ~spl2_28),
% 2.13/0.63    inference(avatar_component_clause,[],[f592])).
% 2.13/0.63  fof(f592,plain,(
% 2.13/0.63    spl2_28 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 2.13/0.63  fof(f65,plain,(
% 2.13/0.63    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f37])).
% 2.13/0.63  fof(f37,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.13/0.63    inference(ennf_transformation,[],[f26])).
% 2.13/0.63  fof(f26,axiom,(
% 2.13/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.13/0.63  fof(f1558,plain,(
% 2.13/0.63    ~spl2_1 | spl2_27),
% 2.13/0.63    inference(avatar_split_clause,[],[f1557,f588,f84])).
% 2.13/0.63  fof(f84,plain,(
% 2.13/0.63    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.13/0.63  fof(f588,plain,(
% 2.13/0.63    spl2_27 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 2.13/0.63  fof(f1557,plain,(
% 2.13/0.63    ~v3_pre_topc(sK1,sK0) | spl2_27),
% 2.13/0.63    inference(subsumption_resolution,[],[f1556,f59])).
% 2.13/0.63  fof(f1556,plain,(
% 2.13/0.63    ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl2_27),
% 2.13/0.63    inference(subsumption_resolution,[],[f1555,f60])).
% 2.13/0.63  fof(f1555,plain,(
% 2.13/0.63    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_27),
% 2.13/0.63    inference(subsumption_resolution,[],[f622,f82])).
% 2.13/0.63  fof(f82,plain,(
% 2.13/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.13/0.63    inference(equality_resolution,[],[f75])).
% 2.13/0.63  fof(f75,plain,(
% 2.13/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.13/0.63    inference(cnf_transformation,[],[f57])).
% 2.13/0.63  fof(f57,plain,(
% 2.13/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.13/0.63    inference(flattening,[],[f56])).
% 2.13/0.63  fof(f56,plain,(
% 2.13/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.13/0.63    inference(nnf_transformation,[],[f2])).
% 2.13/0.63  fof(f2,axiom,(
% 2.13/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.13/0.63  fof(f622,plain,(
% 2.13/0.63    ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_27),
% 2.13/0.63    inference(duplicate_literal_removal,[],[f619])).
% 2.13/0.63  fof(f619,plain,(
% 2.13/0.63    ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_27),
% 2.13/0.63    inference(resolution,[],[f590,f69])).
% 2.13/0.63  fof(f69,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f42])).
% 2.13/0.63  fof(f42,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.13/0.63    inference(flattening,[],[f41])).
% 2.13/0.63  fof(f41,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.13/0.63    inference(ennf_transformation,[],[f27])).
% 2.13/0.63  fof(f27,axiom,(
% 2.13/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 2.13/0.63  fof(f590,plain,(
% 2.13/0.63    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl2_27),
% 2.13/0.63    inference(avatar_component_clause,[],[f588])).
% 2.13/0.63  fof(f1554,plain,(
% 2.13/0.63    spl2_1 | ~spl2_28),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f1553])).
% 2.13/0.63  fof(f1553,plain,(
% 2.13/0.63    $false | (spl2_1 | ~spl2_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1552,f58])).
% 2.13/0.63  fof(f58,plain,(
% 2.13/0.63    v2_pre_topc(sK0)),
% 2.13/0.63    inference(cnf_transformation,[],[f54])).
% 2.13/0.63  fof(f1552,plain,(
% 2.13/0.63    ~v2_pre_topc(sK0) | (spl2_1 | ~spl2_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1551,f59])).
% 2.13/0.63  fof(f1551,plain,(
% 2.13/0.63    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl2_1 | ~spl2_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1550,f60])).
% 2.13/0.63  fof(f1550,plain,(
% 2.13/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl2_1 | ~spl2_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1536,f86])).
% 2.13/0.63  fof(f86,plain,(
% 2.13/0.63    ~v3_pre_topc(sK1,sK0) | spl2_1),
% 2.13/0.63    inference(avatar_component_clause,[],[f84])).
% 2.13/0.63  fof(f1536,plain,(
% 2.13/0.63    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_28),
% 2.13/0.63    inference(superposition,[],[f70,f594])).
% 2.13/0.63  fof(f70,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f44])).
% 2.13/0.63  fof(f44,plain,(
% 2.13/0.63    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/0.63    inference(flattening,[],[f43])).
% 2.13/0.63  fof(f43,plain,(
% 2.13/0.63    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f25])).
% 2.13/0.63  fof(f25,axiom,(
% 2.13/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.13/0.63  fof(f1504,plain,(
% 2.13/0.63    spl2_28 | ~spl2_2),
% 2.13/0.63    inference(avatar_split_clause,[],[f1503,f88,f592])).
% 2.13/0.63  fof(f1503,plain,(
% 2.13/0.63    sK1 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 2.13/0.63    inference(forward_demodulation,[],[f1502,f272])).
% 2.13/0.63  fof(f272,plain,(
% 2.13/0.63    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_2),
% 2.13/0.63    inference(forward_demodulation,[],[f268,f271])).
% 2.13/0.63  fof(f271,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.13/0.63    inference(forward_demodulation,[],[f267,f142])).
% 2.13/0.63  fof(f142,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.13/0.63    inference(subsumption_resolution,[],[f140,f115])).
% 2.13/0.63  fof(f115,plain,(
% 2.13/0.63    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.63    inference(subsumption_resolution,[],[f102,f59])).
% 2.13/0.63  fof(f102,plain,(
% 2.13/0.63    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.13/0.63    inference(resolution,[],[f60,f64])).
% 2.13/0.63  fof(f64,plain,(
% 2.13/0.63    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f36])).
% 2.13/0.63  fof(f36,plain,(
% 2.13/0.63    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.13/0.63    inference(flattening,[],[f35])).
% 2.13/0.63  fof(f35,plain,(
% 2.13/0.63    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f23])).
% 2.13/0.63  fof(f23,axiom,(
% 2.13/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.13/0.63  fof(f140,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 2.13/0.63    inference(superposition,[],[f89,f63])).
% 2.13/0.63  fof(f63,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f34])).
% 2.13/0.63  fof(f34,plain,(
% 2.13/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f16])).
% 2.13/0.63  fof(f16,axiom,(
% 2.13/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.13/0.63  fof(f89,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.13/0.63    inference(avatar_component_clause,[],[f88])).
% 2.13/0.63  fof(f267,plain,(
% 2.13/0.63    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 2.13/0.63    inference(resolution,[],[f147,f79])).
% 2.13/0.63  fof(f79,plain,(
% 2.13/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f48])).
% 2.13/0.63  fof(f48,plain,(
% 2.13/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f12])).
% 2.13/0.63  fof(f12,axiom,(
% 2.13/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.13/0.63  fof(f147,plain,(
% 2.13/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.13/0.63    inference(resolution,[],[f117,f74])).
% 2.13/0.63  fof(f74,plain,(
% 2.13/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f55])).
% 2.13/0.63  fof(f55,plain,(
% 2.13/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.13/0.63    inference(nnf_transformation,[],[f21])).
% 2.13/0.63  fof(f21,axiom,(
% 2.13/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.13/0.63  fof(f117,plain,(
% 2.13/0.63    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.13/0.63    inference(subsumption_resolution,[],[f104,f59])).
% 2.13/0.63  fof(f104,plain,(
% 2.13/0.63    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.13/0.63    inference(resolution,[],[f60,f66])).
% 2.13/0.63  fof(f66,plain,(
% 2.13/0.63    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f38])).
% 2.13/0.63  fof(f38,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.13/0.63    inference(ennf_transformation,[],[f24])).
% 2.13/0.63  fof(f24,axiom,(
% 2.13/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.13/0.63  fof(f268,plain,(
% 2.13/0.63    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 2.13/0.63    inference(resolution,[],[f147,f78])).
% 2.13/0.63  fof(f78,plain,(
% 2.13/0.63    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f47])).
% 2.13/0.63  fof(f47,plain,(
% 2.13/0.63    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f15])).
% 2.13/0.63  fof(f15,axiom,(
% 2.13/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.13/0.63  fof(f1502,plain,(
% 2.13/0.63    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.13/0.63    inference(forward_demodulation,[],[f1498,f1501])).
% 2.13/0.63  fof(f1501,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.13/0.63    inference(forward_demodulation,[],[f1497,f344])).
% 2.13/0.63  fof(f344,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.13/0.63    inference(subsumption_resolution,[],[f342,f115])).
% 2.13/0.63  fof(f342,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.63    inference(superposition,[],[f116,f63])).
% 2.13/0.63  fof(f116,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.13/0.63    inference(subsumption_resolution,[],[f103,f59])).
% 2.13/0.63  fof(f103,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.13/0.63    inference(resolution,[],[f60,f65])).
% 2.13/0.63  fof(f1497,plain,(
% 2.13/0.63    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.13/0.63    inference(resolution,[],[f757,f79])).
% 2.13/0.63  fof(f757,plain,(
% 2.13/0.63    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.13/0.63    inference(resolution,[],[f567,f74])).
% 2.13/0.63  fof(f567,plain,(
% 2.13/0.63    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 2.13/0.63    inference(superposition,[],[f431,f265])).
% 2.13/0.63  fof(f265,plain,(
% 2.13/0.63    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.13/0.63    inference(subsumption_resolution,[],[f264,f59])).
% 2.13/0.63  fof(f264,plain,(
% 2.13/0.63    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.13/0.63    inference(subsumption_resolution,[],[f262,f60])).
% 2.13/0.63  fof(f262,plain,(
% 2.13/0.63    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.13/0.63    inference(superposition,[],[f114,f67])).
% 2.13/0.63  fof(f67,plain,(
% 2.13/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f39])).
% 2.13/0.63  fof(f39,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.13/0.63    inference(ennf_transformation,[],[f29])).
% 2.13/0.63  fof(f29,axiom,(
% 2.13/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.13/0.63  fof(f114,plain,(
% 2.13/0.63    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)) )),
% 2.13/0.63    inference(resolution,[],[f60,f63])).
% 2.13/0.63  fof(f431,plain,(
% 2.13/0.63    ( ! [X3] : (r1_tarski(k4_xboole_0(sK1,X3),k2_pre_topc(sK0,sK1))) )),
% 2.13/0.63    inference(resolution,[],[f149,f71])).
% 2.13/0.63  fof(f71,plain,(
% 2.13/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f7])).
% 2.13/0.63  fof(f7,axiom,(
% 2.13/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.13/0.63  fof(f149,plain,(
% 2.13/0.63    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(X1,k2_pre_topc(sK0,sK1))) )),
% 2.13/0.63    inference(resolution,[],[f117,f72])).
% 2.13/0.63  fof(f72,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f46])).
% 2.13/0.63  fof(f46,plain,(
% 2.13/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.13/0.63    inference(flattening,[],[f45])).
% 2.13/0.63  fof(f45,plain,(
% 2.13/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.13/0.63    inference(ennf_transformation,[],[f5])).
% 2.13/0.63  fof(f5,axiom,(
% 2.13/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.13/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.13/0.63  fof(f1498,plain,(
% 2.13/0.63    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 2.13/0.63    inference(resolution,[],[f757,f78])).
% 2.13/0.63  fof(f596,plain,(
% 2.13/0.63    ~spl2_27 | spl2_28),
% 2.13/0.63    inference(avatar_split_clause,[],[f582,f592,f588])).
% 2.13/0.63  fof(f582,plain,(
% 2.13/0.63    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.13/0.63    inference(resolution,[],[f570,f77])).
% 2.13/0.63  fof(f77,plain,(
% 2.13/0.63    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f57])).
% 2.13/0.63  fof(f570,plain,(
% 2.13/0.63    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.13/0.63    inference(superposition,[],[f71,f265])).
% 2.13/0.63  fof(f92,plain,(
% 2.13/0.63    spl2_1 | spl2_2),
% 2.13/0.63    inference(avatar_split_clause,[],[f61,f88,f84])).
% 2.13/0.63  fof(f61,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.13/0.63    inference(cnf_transformation,[],[f54])).
% 2.13/0.63  fof(f91,plain,(
% 2.13/0.63    ~spl2_1 | ~spl2_2),
% 2.13/0.63    inference(avatar_split_clause,[],[f62,f88,f84])).
% 2.13/0.63  fof(f62,plain,(
% 2.13/0.63    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.13/0.63    inference(cnf_transformation,[],[f54])).
% 2.13/0.63  % SZS output end Proof for theBenchmark
% 2.13/0.63  % (6504)------------------------------
% 2.13/0.63  % (6504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.63  % (6504)Termination reason: Refutation
% 2.13/0.63  
% 2.13/0.63  % (6504)Memory used [KB]: 11385
% 2.13/0.63  % (6504)Time elapsed: 0.235 s
% 2.13/0.63  % (6504)------------------------------
% 2.13/0.63  % (6504)------------------------------
% 2.22/0.66  % (6487)Success in time 0.3 s
%------------------------------------------------------------------------------
