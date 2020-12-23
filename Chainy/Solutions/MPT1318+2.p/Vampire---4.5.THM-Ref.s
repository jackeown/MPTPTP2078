%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1318+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 177 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  138 ( 665 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4382,plain,(
    $false ),
    inference(resolution,[],[f4370,f3948])).

fof(f3948,plain,(
    ~ m1_subset_1(k3_xboole_0(sK3,sK4),k1_zfmisc_1(sK4)) ),
    inference(backward_demodulation,[],[f3742,f3906])).

fof(f3906,plain,(
    k3_xboole_0(sK4,sK3) = k3_xboole_0(sK3,sK4) ),
    inference(superposition,[],[f2725,f3446])).

fof(f3446,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK2),sK3,X0) = k3_xboole_0(X0,sK3) ),
    inference(forward_demodulation,[],[f2676,f2677])).

fof(f2677,plain,(
    ! [X1] : k3_xboole_0(X1,sK3) = k9_subset_1(u1_struct_0(sK2),X1,sK3) ),
    inference(resolution,[],[f2527,f2547])).

fof(f2547,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2406])).

fof(f2406,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f2527,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f2472])).

fof(f2472,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f2387,f2471,f2470,f2469])).

fof(f2469,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2470,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X2))))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X2))))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f2471,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X2))))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f2387,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2374])).

fof(f2374,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    inference(negated_conjecture,[],[f2373])).

fof(f2373,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

fof(f2676,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(resolution,[],[f2527,f2546])).

fof(f2546,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f2405])).

fof(f2405,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f454])).

fof(f454,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f2725,plain,(
    ! [X1] : k3_xboole_0(X1,sK4) = k9_subset_1(u1_struct_0(sK2),X1,sK4) ),
    inference(resolution,[],[f2528,f2547])).

fof(f2528,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f2472])).

fof(f3742,plain,(
    ~ m1_subset_1(k3_xboole_0(sK4,sK3),k1_zfmisc_1(sK4)) ),
    inference(backward_demodulation,[],[f3703,f3705])).

fof(f3705,plain,(
    sK4 = u1_struct_0(k1_pre_topc(sK2,sK4)) ),
    inference(resolution,[],[f2528,f2658])).

fof(f2658,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK2)))
      | u1_struct_0(k1_pre_topc(sK2,X8)) = X8 ) ),
    inference(resolution,[],[f2526,f2545])).

fof(f2545,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2404])).

fof(f2404,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1829])).

fof(f1829,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f2526,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2472])).

fof(f3703,plain,(
    ~ m1_subset_1(k3_xboole_0(sK4,sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) ),
    inference(forward_demodulation,[],[f2529,f3446])).

fof(f2529,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) ),
    inference(cnf_transformation,[],[f2472])).

fof(f4370,plain,(
    ! [X2] : m1_subset_1(k3_xboole_0(X2,sK4),k1_zfmisc_1(sK4)) ),
    inference(backward_demodulation,[],[f4204,f4203])).

fof(f4203,plain,(
    ! [X1] : k3_xboole_0(X1,sK4) = k9_subset_1(sK4,X1,sK4) ),
    inference(resolution,[],[f4200,f2547])).

fof(f4200,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK4)) ),
    inference(resolution,[],[f4199,f2613])).

fof(f2613,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2501])).

fof(f2501,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f4199,plain,(
    r1_tarski(sK4,sK4) ),
    inference(subsumption_resolution,[],[f4198,f2528])).

fof(f4198,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,sK4) ),
    inference(duplicate_literal_removal,[],[f4195])).

fof(f4195,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,sK4)
    | r1_tarski(sK4,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f2737,f2622])).

fof(f2622,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK16(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2511])).

fof(f2511,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK16(X0,X1,X2),X2)
            & r2_hidden(sK16(X0,X1,X2),X1)
            & m1_subset_1(sK16(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f2453,f2510])).

fof(f2510,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK16(X0,X1,X2),X2)
        & r2_hidden(sK16(X0,X1,X2),X1)
        & m1_subset_1(sK16(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2453,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2452])).

fof(f2452,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f538])).

fof(f538,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f2737,plain,(
    ! [X15] :
      ( r2_hidden(sK16(u1_struct_0(sK2),sK4,X15),sK4)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(sK4,X15) ) ),
    inference(resolution,[],[f2528,f2621])).

fof(f2621,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK16(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f2511])).

fof(f4204,plain,(
    ! [X2] : m1_subset_1(k9_subset_1(sK4,X2,sK4),k1_zfmisc_1(sK4)) ),
    inference(resolution,[],[f4200,f2548])).

fof(f2548,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2407])).

fof(f2407,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f472])).

fof(f472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
%------------------------------------------------------------------------------
