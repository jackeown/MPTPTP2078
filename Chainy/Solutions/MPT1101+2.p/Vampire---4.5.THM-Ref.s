%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1101+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:07 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   23 (  35 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 (  91 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3946,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3945,f2793])).

fof(f2793,plain,(
    l1_struct_0(sK68) ),
    inference(cnf_transformation,[],[f2443])).

fof(f2443,plain,
    ( k2_struct_0(sK68) != k4_subset_1(u1_struct_0(sK68),sK69,k3_subset_1(u1_struct_0(sK68),sK69))
    & m1_subset_1(sK69,k1_zfmisc_1(u1_struct_0(sK68)))
    & l1_struct_0(sK68) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK68,sK69])],[f1780,f2442,f2441])).

fof(f2441,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( k2_struct_0(sK68) != k4_subset_1(u1_struct_0(sK68),X1,k3_subset_1(u1_struct_0(sK68),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK68))) )
      & l1_struct_0(sK68) ) ),
    introduced(choice_axiom,[])).

fof(f2442,plain,
    ( ? [X1] :
        ( k2_struct_0(sK68) != k4_subset_1(u1_struct_0(sK68),X1,k3_subset_1(u1_struct_0(sK68),X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK68))) )
   => ( k2_struct_0(sK68) != k4_subset_1(u1_struct_0(sK68),sK69,k3_subset_1(u1_struct_0(sK68),sK69))
      & m1_subset_1(sK69,k1_zfmisc_1(u1_struct_0(sK68))) ) ),
    introduced(choice_axiom,[])).

fof(f1780,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1771])).

fof(f1771,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    inference(negated_conjecture,[],[f1770])).

fof(f1770,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

fof(f3945,plain,(
    ~ l1_struct_0(sK68) ),
    inference(trivial_inequality_removal,[],[f3944])).

fof(f3944,plain,
    ( u1_struct_0(sK68) != u1_struct_0(sK68)
    | ~ l1_struct_0(sK68) ),
    inference(superposition,[],[f3942,f2840])).

fof(f2840,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1822])).

fof(f1822,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1760])).

fof(f1760,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3942,plain,(
    k2_struct_0(sK68) != u1_struct_0(sK68) ),
    inference(forward_demodulation,[],[f3941,f2996])).

fof(f2996,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f460])).

fof(f460,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f3941,plain,(
    k2_struct_0(sK68) != k2_subset_1(u1_struct_0(sK68)) ),
    inference(subsumption_resolution,[],[f3938,f2794])).

fof(f2794,plain,(
    m1_subset_1(sK69,k1_zfmisc_1(u1_struct_0(sK68))) ),
    inference(cnf_transformation,[],[f2443])).

fof(f3938,plain,
    ( k2_struct_0(sK68) != k2_subset_1(u1_struct_0(sK68))
    | ~ m1_subset_1(sK69,k1_zfmisc_1(u1_struct_0(sK68))) ),
    inference(superposition,[],[f2795,f2809])).

fof(f2809,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1793])).

fof(f1793,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f503])).

fof(f503,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f2795,plain,(
    k2_struct_0(sK68) != k4_subset_1(u1_struct_0(sK68),sK69,k3_subset_1(u1_struct_0(sK68),sK69)) ),
    inference(cnf_transformation,[],[f2443])).
%------------------------------------------------------------------------------
