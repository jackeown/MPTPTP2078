%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1256+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:14 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 211 expanded)
%              Number of leaves         :   10 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 590 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5121,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5120,f2474])).

fof(f2474,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f2374])).

fof(f2374,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2196,f2373,f2372])).

fof(f2372,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2373,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2196,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2144])).

fof(f2144,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f2143])).

fof(f2143,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

fof(f5120,plain,(
    r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f5119,f3477])).

fof(f3477,plain,(
    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3207,f3299])).

fof(f3299,plain,(
    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f2751,f2600])).

fof(f2600,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2296])).

fof(f2296,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2751,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2472,f2473,f2504])).

fof(f2504,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2219])).

fof(f2219,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2218])).

fof(f2218,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f2473,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2374])).

fof(f2472,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2374])).

fof(f3207,plain,(
    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f2472,f2751,f2500])).

fof(f2500,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2213])).

fof(f2213,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2134])).

fof(f2134,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f5119,plain,(
    r1_tarski(k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f5118,f5052])).

fof(f5052,plain,(
    k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f5051,f3299])).

fof(f5051,plain,(
    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f4680,f2842])).

fof(f2842,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f2802,f2803])).

fof(f2803,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f2473,f2600])).

fof(f2802,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f2473,f2599])).

fof(f2599,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2295])).

fof(f2295,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f4680,plain,(
    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) ),
    inference(unit_resulting_resolution,[],[f2472,f2837,f2677])).

fof(f2677,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2370])).

fof(f2370,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2087])).

fof(f2087,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f2837,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f2804,f2803])).

fof(f2804,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2473,f2601])).

fof(f2601,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2297])).

fof(f2297,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f5118,plain,(
    r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4633,f2877])).

fof(f2877,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f2747,f2803])).

fof(f2747,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f2472,f2473,f2500])).

fof(f4633,plain,(
    r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f2472,f2837,f2502])).

fof(f2502,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2215])).

fof(f2215,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2142])).

fof(f2142,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).
%------------------------------------------------------------------------------
