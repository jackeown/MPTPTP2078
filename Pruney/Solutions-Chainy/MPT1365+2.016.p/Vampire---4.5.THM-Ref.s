%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 245 expanded)
%              Number of leaves         :   11 (  92 expanded)
%              Depth                    :   21
%              Number of atoms          :  308 (1905 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(subsumption_resolution,[],[f157,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f157,plain,(
    ~ r1_tarski(k3_xboole_0(sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f152,f32])).

fof(f32,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v2_compts_1(X2,sK0)
            & v2_compts_1(X1,sK0)
            & v8_pre_topc(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v2_compts_1(X2,sK0)
          & v2_compts_1(sK1,sK0)
          & v8_pre_topc(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v2_compts_1(X2,sK0)
        & v2_compts_1(sK1,sK0)
        & v8_pre_topc(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v2_compts_1(sK2,sK0)
      & v2_compts_1(sK1,sK0)
      & v8_pre_topc(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

fof(f152,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | ~ r1_tarski(k3_xboole_0(sK2,sK1),sK2) ),
    inference(resolution,[],[f141,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k3_xboole_0(sK2,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f139,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(sK2,sK1),X0)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f134,f54])).

fof(f54,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(duplicate_literal_removal,[],[f46])).

fof(f46,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f41,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f133,f26])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f27])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f132,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f28])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f29])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f62])).

fof(f62,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f61,f26])).

fof(f61,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f60,f27])).

fof(f60,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f59,f30])).

fof(f30,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,
    ( ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f55,f31])).

fof(f31,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f34,f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

fof(f129,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f66])).

fof(f66,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f65,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f64,f27])).

fof(f64,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f63,f30])).

fof(f63,plain,
    ( ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f56,f32])).

fof(f56,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f34,f29])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(sK2,sK0)
      | ~ v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f125,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

fof(f125,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f124,f29])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ v2_compts_1(X0,sK0)
      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f123,f26])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ v2_compts_1(X0,sK0)
      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f114,f27])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ v2_compts_1(X0,sK0)
      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f69,f33])).

fof(f33,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X4,X2,X5,X3] :
      ( v2_compts_1(k9_subset_1(u1_struct_0(X2),X3,X4),X2)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(X2),X3,X4),X5)
      | ~ v2_compts_1(X5,X2)
      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X2),X3,X4),X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | v2_compts_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (4531)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (4524)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (4533)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (4529)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (4534)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (4524)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f157,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ~r1_tarski(k3_xboole_0(sK2,sK1),sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f152,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    v2_compts_1(sK2,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f9])).
% 0.20/0.47  fof(f9,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    ~v2_compts_1(sK2,sK0) | ~r1_tarski(k3_xboole_0(sK2,sK1),sK2)),
% 0.20/0.47    inference(resolution,[],[f141,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X0,sK0) | ~r1_tarski(k3_xboole_0(sK2,sK1),X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f139,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK2,sK1),X0) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(superposition,[],[f134,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X6,X8,X7] : (k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7) | ~m1_subset_1(X8,k1_zfmisc_1(X6))) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X6,X8,X7] : (k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7) | ~m1_subset_1(X8,k1_zfmisc_1(X6)) | ~m1_subset_1(X8,k1_zfmisc_1(X6))) )),
% 0.20/0.47    inference(superposition,[],[f41,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f133,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f132,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f131,f28])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f130,f29])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f129,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    v4_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f61,f26])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f60,f27])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f59,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    v8_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ~v8_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f55,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    v2_compts_1(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ~v2_compts_1(sK1,sK0) | ~v8_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(resolution,[],[f34,f28])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f126,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    v4_pre_topc(sK2,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f65,f26])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    v4_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f64,f27])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    v4_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f63,f30])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ~v8_pre_topc(sK0) | v4_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f56,f32])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ~v2_compts_1(sK2,sK0) | ~v8_pre_topc(sK0) | v4_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(resolution,[],[f34,f29])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK2,sK0) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f125,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0] : (~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | ~v2_compts_1(X0,sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f124,f29])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~v2_compts_1(X0,sK0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f123,f26])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~v2_compts_1(X0,sK0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f114,f27])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~v2_compts_1(X0,sK0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(resolution,[],[f69,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X4,X2,X5,X3] : (v2_compts_1(k9_subset_1(u1_struct_0(X2),X3,X4),X2) | ~r1_tarski(k9_subset_1(u1_struct_0(X2),X3,X4),X5) | ~v2_compts_1(X5,X2) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X2),X3,X4),X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.20/0.47    inference(resolution,[],[f36,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | v2_compts_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (4524)------------------------------
% 0.20/0.47  % (4524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (4524)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (4524)Memory used [KB]: 1663
% 0.20/0.47  % (4524)Time elapsed: 0.055 s
% 0.20/0.47  % (4524)------------------------------
% 0.20/0.47  % (4524)------------------------------
% 0.20/0.47  % (4520)Success in time 0.115 s
%------------------------------------------------------------------------------
