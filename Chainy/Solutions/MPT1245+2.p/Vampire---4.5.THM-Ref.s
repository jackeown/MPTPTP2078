%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1245+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:14 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   34 (  98 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 401 expanded)
%              Number of equality atoms :   24 ( 101 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3561,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3497,f2556])).

fof(f2556,plain,(
    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(cnf_transformation,[],[f2421])).

fof(f2421,plain,
    ( k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2178,f2420,f2419])).

fof(f2419,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1)))
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2420,plain,
    ( ? [X1] :
        ( k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1)))
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2178,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2177])).

fof(f2177,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2128])).

fof(f2128,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f2127])).

fof(f2127,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

fof(f3497,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(backward_demodulation,[],[f2986,f3493])).

fof(f3493,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f3435,f2988])).

fof(f2988,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f2553,f2554,f2564])).

fof(f2564,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2190])).

fof(f2190,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2116])).

fof(f2116,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f2554,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2421])).

fof(f2553,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2421])).

fof(f3435,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f2977,f2612])).

fof(f2612,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2452])).

fof(f2452,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2451])).

fof(f2451,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2977,plain,(
    r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f2553,f2555,f2896,f2554,f2554,f2559])).

fof(f2559,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2184])).

fof(f2184,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2183])).

fof(f2183,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2124])).

fof(f2124,axiom,(
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

fof(f2896,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2610])).

fof(f2610,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2452])).

fof(f2555,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2421])).

fof(f2986,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f2553,f2554,f2562])).

fof(f2562,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2188])).

fof(f2188,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2126])).

fof(f2126,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).
%------------------------------------------------------------------------------
