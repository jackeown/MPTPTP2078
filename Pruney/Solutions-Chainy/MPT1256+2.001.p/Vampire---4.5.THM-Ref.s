%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:27 EST 2020

% Result     : Theorem 4.46s
% Output     : Refutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 348 expanded)
%              Number of leaves         :   18 ( 114 expanded)
%              Depth                    :   17
%              Number of atoms          :  249 ( 986 expanded)
%              Number of equality atoms :   49 (  79 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10786,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f7880,f8378,f10772])).

fof(f10772,plain,
    ( ~ spl2_3
    | ~ spl2_66 ),
    inference(avatar_contradiction_clause,[],[f10771])).

fof(f10771,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_66 ),
    inference(subsumption_resolution,[],[f10766,f57])).

fof(f57,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f49,f48])).

fof(f48,plain,
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

fof(f49,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

fof(f10766,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_66 ),
    inference(backward_demodulation,[],[f2302,f8469])).

fof(f8469,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl2_66 ),
    inference(subsumption_resolution,[],[f8441,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f8441,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_66 ),
    inference(resolution,[],[f1342,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f1342,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f1341])).

fof(f1341,plain,
    ( spl2_66
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f2302,plain,
    ( r1_tarski(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f2301,f153])).

fof(f153,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f152,f90])).

fof(f90,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f56,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f152,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f136,f55])).

fof(f136,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f121,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f121,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_3
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f2301,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f157,f103])).

fof(f103,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f87,f55])).

fof(f87,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f59])).

fof(f157,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f139,f55])).

fof(f139,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f121,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tops_1)).

fof(f8378,plain,
    ( ~ spl2_3
    | spl2_66
    | ~ spl2_228 ),
    inference(avatar_contradiction_clause,[],[f8377])).

fof(f8377,plain,
    ( $false
    | ~ spl2_3
    | spl2_66
    | ~ spl2_228 ),
    inference(subsumption_resolution,[],[f4326,f4271])).

fof(f4271,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_228 ),
    inference(avatar_component_clause,[],[f4270])).

fof(f4270,plain,
    ( spl2_228
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_228])])).

fof(f4326,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | spl2_66 ),
    inference(subsumption_resolution,[],[f4268,f1343])).

fof(f1343,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_66 ),
    inference(avatar_component_clause,[],[f1341])).

fof(f4268,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(superposition,[],[f62,f1418])).

fof(f1418,plain,
    ( k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f1417,f289])).

fof(f289,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f286,f102])).

fof(f102,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f55])).

fof(f86,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f286,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f100,f206])).

fof(f206,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f205,f55])).

fof(f205,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f204,f121])).

fof(f204,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f71,f103])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f100,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X8,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,X8) ) ),
    inference(resolution,[],[f56,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f1417,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f1408,f212])).

fof(f212,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_3 ),
    inference(resolution,[],[f206,f64])).

fof(f1408,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f369,f206])).

fof(f369,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3)),sK1) ) ),
    inference(resolution,[],[f93,f62])).

fof(f93,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X2,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X2),sK1) ) ),
    inference(resolution,[],[f56,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f7880,plain,
    ( ~ spl2_3
    | spl2_228 ),
    inference(avatar_contradiction_clause,[],[f7879])).

fof(f7879,plain,
    ( $false
    | ~ spl2_3
    | spl2_228 ),
    inference(subsumption_resolution,[],[f7876,f4272])).

fof(f4272,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_228 ),
    inference(avatar_component_clause,[],[f4270])).

fof(f7876,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(superposition,[],[f1555,f1793])).

fof(f1793,plain,
    ( k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f1544,f206])).

fof(f1544,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),X3),k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f357,f148])).

fof(f148,plain,
    ( ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(X5,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f121,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f357,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3),sK1) = k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3),k3_subset_1(u1_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f92,f62])).

fof(f92,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),X1,k3_subset_1(u1_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f56,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f1555,plain,
    ( ! [X1] : m1_subset_1(k3_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1551,f121])).

fof(f1551,plain,
    ( ! [X1] :
        ( m1_subset_1(k3_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_3 ),
    inference(superposition,[],[f77,f148])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f135,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f132,f56])).

fof(f132,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(resolution,[],[f122,f62])).

fof(f122,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:41:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (32750)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (32747)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (32746)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (32762)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (32763)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (32754)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (32744)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.19/0.51  % (32755)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.19/0.52  % (32759)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.19/0.52  % (32743)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.52  % (32745)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.19/0.52  % (32760)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.19/0.52  % (32758)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.19/0.52  % (32752)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.19/0.52  % (32756)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.19/0.53  % (32742)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.19/0.53  % (32748)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.35/0.53  % (32753)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.35/0.53  % (32749)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.35/0.54  % (32761)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.35/0.54  % (32757)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.35/0.54  % (32751)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.35/0.54  % (32764)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.35/0.54  % (32767)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.35/0.55  % (32765)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.35/0.55  % (32766)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.08/0.64  % (32751)Refutation not found, incomplete strategy% (32751)------------------------------
% 2.08/0.64  % (32751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.64  % (32751)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.64  
% 2.08/0.64  % (32751)Memory used [KB]: 6140
% 2.08/0.64  % (32751)Time elapsed: 0.230 s
% 2.08/0.64  % (32751)------------------------------
% 2.08/0.64  % (32751)------------------------------
% 3.66/0.92  % (32742)Time limit reached!
% 3.66/0.92  % (32742)------------------------------
% 3.66/0.92  % (32742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.93  % (32742)Termination reason: Time limit
% 3.66/0.93  
% 3.66/0.93  % (32742)Memory used [KB]: 14839
% 3.66/0.93  % (32742)Time elapsed: 0.506 s
% 3.66/0.93  % (32742)------------------------------
% 3.66/0.93  % (32742)------------------------------
% 4.46/0.93  % (32755)Time limit reached!
% 4.46/0.93  % (32755)------------------------------
% 4.46/0.93  % (32755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.93  % (32755)Termination reason: Time limit
% 4.46/0.93  
% 4.46/0.93  % (32755)Memory used [KB]: 11385
% 4.46/0.93  % (32755)Time elapsed: 0.516 s
% 4.46/0.93  % (32755)------------------------------
% 4.46/0.93  % (32755)------------------------------
% 4.46/0.95  % (32756)Time limit reached!
% 4.46/0.95  % (32756)------------------------------
% 4.46/0.95  % (32756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.95  % (32756)Termination reason: Time limit
% 4.46/0.95  
% 4.46/0.95  % (32756)Memory used [KB]: 7419
% 4.46/0.95  % (32756)Time elapsed: 0.507 s
% 4.46/0.95  % (32756)------------------------------
% 4.46/0.95  % (32756)------------------------------
% 4.46/0.96  % (32743)Refutation found. Thanks to Tanya!
% 4.46/0.96  % SZS status Theorem for theBenchmark
% 4.46/0.96  % SZS output start Proof for theBenchmark
% 4.46/0.96  fof(f10786,plain,(
% 4.46/0.96    $false),
% 4.46/0.96    inference(avatar_sat_refutation,[],[f135,f7880,f8378,f10772])).
% 4.46/0.96  fof(f10772,plain,(
% 4.46/0.96    ~spl2_3 | ~spl2_66),
% 4.46/0.96    inference(avatar_contradiction_clause,[],[f10771])).
% 4.46/0.96  fof(f10771,plain,(
% 4.46/0.96    $false | (~spl2_3 | ~spl2_66)),
% 4.46/0.96    inference(subsumption_resolution,[],[f10766,f57])).
% 4.46/0.96  fof(f57,plain,(
% 4.46/0.96    ~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 4.46/0.96    inference(cnf_transformation,[],[f50])).
% 4.46/0.96  fof(f50,plain,(
% 4.46/0.96    (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 4.46/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f49,f48])).
% 4.46/0.96  fof(f48,plain,(
% 4.46/0.96    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 4.46/0.96    introduced(choice_axiom,[])).
% 4.46/0.96  fof(f49,plain,(
% 4.46/0.96    ? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.46/0.96    introduced(choice_axiom,[])).
% 4.46/0.96  fof(f24,plain,(
% 4.46/0.96    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.46/0.96    inference(ennf_transformation,[],[f23])).
% 4.46/0.96  fof(f23,negated_conjecture,(
% 4.46/0.96    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 4.46/0.96    inference(negated_conjecture,[],[f22])).
% 4.46/0.96  fof(f22,conjecture,(
% 4.46/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).
% 4.46/0.96  fof(f10766,plain,(
% 4.46/0.96    r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_66)),
% 4.46/0.96    inference(backward_demodulation,[],[f2302,f8469])).
% 4.46/0.96  fof(f8469,plain,(
% 4.46/0.96    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~spl2_66),
% 4.46/0.96    inference(subsumption_resolution,[],[f8441,f55])).
% 4.46/0.96  fof(f55,plain,(
% 4.46/0.96    l1_pre_topc(sK0)),
% 4.46/0.96    inference(cnf_transformation,[],[f50])).
% 4.46/0.96  fof(f8441,plain,(
% 4.46/0.96    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0) | ~spl2_66),
% 4.46/0.96    inference(resolution,[],[f1342,f59])).
% 4.46/0.96  fof(f59,plain,(
% 4.46/0.96    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f26])).
% 4.46/0.96  fof(f26,plain,(
% 4.46/0.96    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.46/0.96    inference(ennf_transformation,[],[f19])).
% 4.46/0.96  fof(f19,axiom,(
% 4.46/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 4.46/0.96  fof(f1342,plain,(
% 4.46/0.96    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_66),
% 4.46/0.96    inference(avatar_component_clause,[],[f1341])).
% 4.46/0.96  fof(f1341,plain,(
% 4.46/0.96    spl2_66 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 4.46/0.96  fof(f2302,plain,(
% 4.46/0.96    r1_tarski(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_tops_1(sK0,sK1)) | ~spl2_3),
% 4.46/0.96    inference(forward_demodulation,[],[f2301,f153])).
% 4.46/0.96  fof(f153,plain,(
% 4.46/0.96    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | ~spl2_3),
% 4.46/0.96    inference(forward_demodulation,[],[f152,f90])).
% 4.46/0.96  fof(f90,plain,(
% 4.46/0.96    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 4.46/0.96    inference(resolution,[],[f56,f64])).
% 4.46/0.96  fof(f64,plain,(
% 4.46/0.96    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 4.46/0.96    inference(cnf_transformation,[],[f31])).
% 4.46/0.96  fof(f31,plain,(
% 4.46/0.96    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.46/0.96    inference(ennf_transformation,[],[f7])).
% 4.46/0.96  fof(f7,axiom,(
% 4.46/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 4.46/0.96  fof(f56,plain,(
% 4.46/0.96    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.96    inference(cnf_transformation,[],[f50])).
% 4.46/0.96  fof(f152,plain,(
% 4.46/0.96    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_3),
% 4.46/0.96    inference(subsumption_resolution,[],[f136,f55])).
% 4.46/0.96  fof(f136,plain,(
% 4.46/0.96    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~l1_pre_topc(sK0) | ~spl2_3),
% 4.46/0.96    inference(resolution,[],[f121,f61])).
% 4.46/0.96  fof(f61,plain,(
% 4.46/0.96    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f28])).
% 4.46/0.96  fof(f28,plain,(
% 4.46/0.96    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.46/0.96    inference(ennf_transformation,[],[f17])).
% 4.46/0.96  fof(f17,axiom,(
% 4.46/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 4.46/0.96  fof(f121,plain,(
% 4.46/0.96    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 4.46/0.96    inference(avatar_component_clause,[],[f120])).
% 4.46/0.96  fof(f120,plain,(
% 4.46/0.96    spl2_3 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 4.46/0.96  fof(f2301,plain,(
% 4.46/0.96    r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1)) | ~spl2_3),
% 4.46/0.96    inference(forward_demodulation,[],[f157,f103])).
% 4.46/0.96  fof(f103,plain,(
% 4.46/0.96    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 4.46/0.96    inference(subsumption_resolution,[],[f87,f55])).
% 4.46/0.96  fof(f87,plain,(
% 4.46/0.96    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 4.46/0.96    inference(resolution,[],[f56,f59])).
% 4.46/0.96  fof(f157,plain,(
% 4.46/0.96    r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_3),
% 4.46/0.96    inference(subsumption_resolution,[],[f139,f55])).
% 4.46/0.96  fof(f139,plain,(
% 4.46/0.96    r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~spl2_3),
% 4.46/0.96    inference(resolution,[],[f121,f58])).
% 4.46/0.96  fof(f58,plain,(
% 4.46/0.96    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f25])).
% 4.46/0.96  fof(f25,plain,(
% 4.46/0.96    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.46/0.96    inference(ennf_transformation,[],[f21])).
% 4.46/0.96  fof(f21,axiom,(
% 4.46/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tops_1)).
% 4.46/0.96  fof(f8378,plain,(
% 4.46/0.96    ~spl2_3 | spl2_66 | ~spl2_228),
% 4.46/0.96    inference(avatar_contradiction_clause,[],[f8377])).
% 4.46/0.96  fof(f8377,plain,(
% 4.46/0.96    $false | (~spl2_3 | spl2_66 | ~spl2_228)),
% 4.46/0.96    inference(subsumption_resolution,[],[f4326,f4271])).
% 4.46/0.96  fof(f4271,plain,(
% 4.46/0.96    m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_228),
% 4.46/0.96    inference(avatar_component_clause,[],[f4270])).
% 4.46/0.96  fof(f4270,plain,(
% 4.46/0.96    spl2_228 <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_228])])).
% 4.46/0.96  fof(f4326,plain,(
% 4.46/0.96    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | spl2_66)),
% 4.46/0.96    inference(subsumption_resolution,[],[f4268,f1343])).
% 4.46/0.96  fof(f1343,plain,(
% 4.46/0.96    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_66),
% 4.46/0.96    inference(avatar_component_clause,[],[f1341])).
% 4.46/0.96  fof(f4268,plain,(
% 4.46/0.96    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 4.46/0.96    inference(superposition,[],[f62,f1418])).
% 4.46/0.96  fof(f1418,plain,(
% 4.46/0.96    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1)) | ~spl2_3),
% 4.46/0.96    inference(forward_demodulation,[],[f1417,f289])).
% 4.46/0.96  fof(f289,plain,(
% 4.46/0.96    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl2_3),
% 4.46/0.96    inference(forward_demodulation,[],[f286,f102])).
% 4.46/0.96  fof(f102,plain,(
% 4.46/0.96    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 4.46/0.96    inference(subsumption_resolution,[],[f86,f55])).
% 4.46/0.96  fof(f86,plain,(
% 4.46/0.96    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 4.46/0.96    inference(resolution,[],[f56,f60])).
% 4.46/0.96  fof(f60,plain,(
% 4.46/0.96    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f27])).
% 4.46/0.96  fof(f27,plain,(
% 4.46/0.96    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.46/0.96    inference(ennf_transformation,[],[f20])).
% 4.46/0.96  fof(f20,axiom,(
% 4.46/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 4.46/0.96  fof(f286,plain,(
% 4.46/0.96    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl2_3),
% 4.46/0.96    inference(resolution,[],[f100,f206])).
% 4.46/0.96  fof(f206,plain,(
% 4.46/0.96    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 4.46/0.96    inference(subsumption_resolution,[],[f205,f55])).
% 4.46/0.96  fof(f205,plain,(
% 4.46/0.96    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_3),
% 4.46/0.96    inference(subsumption_resolution,[],[f204,f121])).
% 4.46/0.96  fof(f204,plain,(
% 4.46/0.96    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 4.46/0.96    inference(superposition,[],[f71,f103])).
% 4.46/0.96  fof(f71,plain,(
% 4.46/0.96    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f39])).
% 4.46/0.96  fof(f39,plain,(
% 4.46/0.96    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.46/0.96    inference(flattening,[],[f38])).
% 4.46/0.96  fof(f38,plain,(
% 4.46/0.96    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.46/0.96    inference(ennf_transformation,[],[f18])).
% 4.46/0.96  fof(f18,axiom,(
% 4.46/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 4.46/0.96  fof(f100,plain,(
% 4.46/0.96    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X8,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,X8)) )),
% 4.46/0.96    inference(resolution,[],[f56,f82])).
% 4.46/0.96  fof(f82,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(cnf_transformation,[],[f47])).
% 4.46/0.96  fof(f47,plain,(
% 4.46/0.96    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.46/0.96    inference(flattening,[],[f46])).
% 4.46/0.96  fof(f46,plain,(
% 4.46/0.96    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.46/0.96    inference(ennf_transformation,[],[f2])).
% 4.46/0.96  fof(f2,axiom,(
% 4.46/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 4.46/0.96  fof(f1417,plain,(
% 4.46/0.96    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1)) | ~spl2_3),
% 4.46/0.96    inference(forward_demodulation,[],[f1408,f212])).
% 4.46/0.96  fof(f212,plain,(
% 4.46/0.96    k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_3),
% 4.46/0.96    inference(resolution,[],[f206,f64])).
% 4.46/0.96  fof(f1408,plain,(
% 4.46/0.96    k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),sK1) | ~spl2_3),
% 4.46/0.96    inference(resolution,[],[f369,f206])).
% 4.46/0.96  fof(f369,plain,(
% 4.46/0.96    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3)),sK1)) )),
% 4.46/0.96    inference(resolution,[],[f93,f62])).
% 4.46/0.96  fof(f93,plain,(
% 4.46/0.96    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X2,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X2),sK1)) )),
% 4.46/0.96    inference(resolution,[],[f56,f67])).
% 4.46/0.96  fof(f67,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(cnf_transformation,[],[f34])).
% 4.46/0.96  fof(f34,plain,(
% 4.46/0.96    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.46/0.96    inference(ennf_transformation,[],[f13])).
% 4.46/0.96  fof(f13,axiom,(
% 4.46/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 4.46/0.96  fof(f62,plain,(
% 4.46/0.96    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(cnf_transformation,[],[f29])).
% 4.46/0.96  fof(f29,plain,(
% 4.46/0.96    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.46/0.96    inference(ennf_transformation,[],[f5])).
% 4.46/0.96  fof(f5,axiom,(
% 4.46/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 4.46/0.96  fof(f7880,plain,(
% 4.46/0.96    ~spl2_3 | spl2_228),
% 4.46/0.96    inference(avatar_contradiction_clause,[],[f7879])).
% 4.46/0.96  fof(f7879,plain,(
% 4.46/0.96    $false | (~spl2_3 | spl2_228)),
% 4.46/0.96    inference(subsumption_resolution,[],[f7876,f4272])).
% 4.46/0.96  fof(f4272,plain,(
% 4.46/0.96    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_228),
% 4.46/0.96    inference(avatar_component_clause,[],[f4270])).
% 4.46/0.96  fof(f7876,plain,(
% 4.46/0.96    m1_subset_1(k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 4.46/0.96    inference(superposition,[],[f1555,f1793])).
% 4.46/0.96  fof(f1793,plain,(
% 4.46/0.96    k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_3),
% 4.46/0.96    inference(resolution,[],[f1544,f206])).
% 4.46/0.96  fof(f1544,plain,(
% 4.46/0.96    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),X3),k3_subset_1(u1_struct_0(sK0),sK1))) ) | ~spl2_3),
% 4.46/0.96    inference(backward_demodulation,[],[f357,f148])).
% 4.46/0.96  fof(f148,plain,(
% 4.46/0.96    ( ! [X5] : (k9_subset_1(u1_struct_0(sK0),X5,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(X5,k3_subset_1(u1_struct_0(sK0),sK1))) ) | ~spl2_3),
% 4.46/0.96    inference(resolution,[],[f121,f79])).
% 4.46/0.96  fof(f79,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f42])).
% 4.46/0.96  fof(f42,plain,(
% 4.46/0.96    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.46/0.96    inference(ennf_transformation,[],[f10])).
% 4.46/0.96  fof(f10,axiom,(
% 4.46/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 4.46/0.96  fof(f357,plain,(
% 4.46/0.96    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3),sK1) = k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3),k3_subset_1(u1_struct_0(sK0),sK1))) )),
% 4.46/0.96    inference(resolution,[],[f92,f62])).
% 4.46/0.96  fof(f92,plain,(
% 4.46/0.96    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),X1,k3_subset_1(u1_struct_0(sK0),sK1))) )),
% 4.46/0.96    inference(resolution,[],[f56,f66])).
% 4.46/0.96  fof(f66,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(cnf_transformation,[],[f33])).
% 4.46/0.96  fof(f33,plain,(
% 4.46/0.96    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.46/0.96    inference(ennf_transformation,[],[f12])).
% 4.46/0.96  fof(f12,axiom,(
% 4.46/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 4.46/0.96  fof(f1555,plain,(
% 4.46/0.96    ( ! [X1] : (m1_subset_1(k3_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_3),
% 4.46/0.96    inference(subsumption_resolution,[],[f1551,f121])).
% 4.46/0.96  fof(f1551,plain,(
% 4.46/0.96    ( ! [X1] : (m1_subset_1(k3_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_3),
% 4.46/0.96    inference(superposition,[],[f77,f148])).
% 4.46/0.96  fof(f77,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(cnf_transformation,[],[f40])).
% 4.46/0.96  fof(f40,plain,(
% 4.46/0.96    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.46/0.96    inference(ennf_transformation,[],[f6])).
% 4.46/0.96  fof(f6,axiom,(
% 4.46/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 4.46/0.96  fof(f135,plain,(
% 4.46/0.96    spl2_3),
% 4.46/0.96    inference(avatar_contradiction_clause,[],[f134])).
% 4.46/0.96  fof(f134,plain,(
% 4.46/0.96    $false | spl2_3),
% 4.46/0.96    inference(subsumption_resolution,[],[f132,f56])).
% 4.46/0.96  fof(f132,plain,(
% 4.46/0.96    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 4.46/0.96    inference(resolution,[],[f122,f62])).
% 4.46/0.96  fof(f122,plain,(
% 4.46/0.96    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 4.46/0.96    inference(avatar_component_clause,[],[f120])).
% 4.46/0.96  % SZS output end Proof for theBenchmark
% 4.46/0.96  % (32743)------------------------------
% 4.46/0.96  % (32743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.96  % (32743)Termination reason: Refutation
% 4.46/0.96  
% 4.46/0.96  % (32743)Memory used [KB]: 17014
% 4.46/0.96  % (32743)Time elapsed: 0.535 s
% 4.46/0.96  % (32743)------------------------------
% 4.46/0.96  % (32743)------------------------------
% 4.46/0.96  % (32740)Success in time 0.602 s
%------------------------------------------------------------------------------
