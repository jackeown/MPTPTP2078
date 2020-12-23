%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1105+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:07 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   28 (  39 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   12
%              Number of atoms          :   47 (  72 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3946,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3945,f2808])).

fof(f2808,plain,(
    l1_struct_0(sK68) ),
    inference(cnf_transformation,[],[f2459])).

fof(f2459,plain,
    ( k2_struct_0(sK68) != k3_subset_1(u1_struct_0(sK68),k1_struct_0(sK68))
    & l1_struct_0(sK68) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK68])],[f1786,f2458])).

fof(f2458,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))
        & l1_struct_0(X0) )
   => ( k2_struct_0(sK68) != k3_subset_1(u1_struct_0(sK68),k1_struct_0(sK68))
      & l1_struct_0(sK68) ) ),
    introduced(choice_axiom,[])).

fof(f1786,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1778])).

fof(f1778,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f1777])).

fof(f1777,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

fof(f3945,plain,(
    ~ l1_struct_0(sK68) ),
    inference(trivial_inequality_removal,[],[f3944])).

fof(f3944,plain,
    ( u1_struct_0(sK68) != u1_struct_0(sK68)
    | ~ l1_struct_0(sK68) ),
    inference(superposition,[],[f3943,f2847])).

fof(f2847,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1822])).

fof(f1822,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1761])).

fof(f1761,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3943,plain,(
    k2_struct_0(sK68) != u1_struct_0(sK68) ),
    inference(forward_demodulation,[],[f3942,f3134])).

fof(f3134,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f3942,plain,(
    k2_struct_0(sK68) != k4_xboole_0(u1_struct_0(sK68),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3941,f2892])).

fof(f2892,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3941,plain,
    ( k2_struct_0(sK68) != k4_xboole_0(u1_struct_0(sK68),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK68))) ),
    inference(superposition,[],[f3936,f2835])).

fof(f2835,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1809])).

fof(f1809,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3936,plain,(
    k2_struct_0(sK68) != k3_subset_1(u1_struct_0(sK68),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3934,f2808])).

fof(f3934,plain,
    ( k2_struct_0(sK68) != k3_subset_1(u1_struct_0(sK68),k1_xboole_0)
    | ~ l1_struct_0(sK68) ),
    inference(superposition,[],[f2809,f2839])).

fof(f2839,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1814])).

fof(f1814,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1760])).

fof(f1760,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f2809,plain,(
    k2_struct_0(sK68) != k3_subset_1(u1_struct_0(sK68),k1_struct_0(sK68)) ),
    inference(cnf_transformation,[],[f2459])).
%------------------------------------------------------------------------------
