%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1303+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:17 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   39 (  91 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 408 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4117,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4106,f3919])).

fof(f3919,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK12,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) ),
    inference(backward_demodulation,[],[f3889,f3888])).

fof(f3888,plain,(
    ! [X0] : k4_xboole_0(sK12,X0) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),sK12,X0) ),
    inference(unit_resulting_resolution,[],[f3031,f3405])).

fof(f3405,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2547])).

fof(f2547,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f3031,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) ),
    inference(cnf_transformation,[],[f2787])).

fof(f2787,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),sK12,sK13),sK11)
    & v1_tops_2(sK12,sK11)
    & m1_subset_1(sK13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11))))
    & m1_subset_1(sK12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11))))
    & l1_pre_topc(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f2284,f2786,f2785,f2784])).

fof(f2784,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),X1,X2),sK11)
              & v1_tops_2(X1,sK11)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) )
      & l1_pre_topc(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f2785,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),X1,X2),sK11)
            & v1_tops_2(X1,sK11)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),sK12,X2),sK11)
          & v1_tops_2(sK12,sK11)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) )
      & m1_subset_1(sK12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) ) ),
    introduced(choice_axiom,[])).

fof(f2786,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),sK12,X2),sK11)
        & v1_tops_2(sK12,sK11)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) )
   => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),sK12,sK13),sK11)
      & v1_tops_2(sK12,sK11)
      & m1_subset_1(sK13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) ) ),
    introduced(choice_axiom,[])).

fof(f2284,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2283])).

fof(f2283,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2275])).

fof(f2275,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f2274])).

fof(f2274,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

fof(f3889,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),sK12,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) ),
    inference(unit_resulting_resolution,[],[f3031,f3406])).

fof(f3406,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2548])).

fof(f2548,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f470])).

fof(f470,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f4106,plain,(
    ~ m1_subset_1(k4_xboole_0(sK12,k4_xboole_0(sK12,sK13)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) ),
    inference(unit_resulting_resolution,[],[f3030,f3033,f3031,f3733,f4035,f3078])).

fof(f3078,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2321])).

fof(f2321,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2320])).

fof(f2320,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2270])).

fof(f2270,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(f4035,plain,(
    ~ v1_tops_2(k4_xboole_0(sK12,k4_xboole_0(sK12,sK13)),sK11) ),
    inference(backward_demodulation,[],[f3034,f4029])).

fof(f4029,plain,(
    ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),X0,sK13) = k4_xboole_0(X0,k4_xboole_0(X0,sK13)) ),
    inference(unit_resulting_resolution,[],[f3032,f3651])).

fof(f3651,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f3039,f3192])).

fof(f3192,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f3039,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2288])).

fof(f2288,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f3032,plain,(
    m1_subset_1(sK13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK11)))) ),
    inference(cnf_transformation,[],[f2787])).

fof(f3034,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK11)),sK12,sK13),sK11) ),
    inference(cnf_transformation,[],[f2787])).

fof(f3733,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f3200,f3192])).

fof(f3200,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f3033,plain,(
    v1_tops_2(sK12,sK11) ),
    inference(cnf_transformation,[],[f2787])).

fof(f3030,plain,(
    l1_pre_topc(sK11) ),
    inference(cnf_transformation,[],[f2787])).
%------------------------------------------------------------------------------
