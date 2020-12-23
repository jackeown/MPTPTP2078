%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 286 expanded)
%              Number of leaves         :   14 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          :  291 (2060 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f922,plain,(
    $false ),
    inference(subsumption_resolution,[],[f918,f109])).

fof(f109,plain,(
    ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    inference(backward_demodulation,[],[f35,f91])).

fof(f91,plain,(
    ! [X16] : k9_subset_1(u1_struct_0(sK0),X16,sK2) = k1_setfam_1(k2_tarski(X16,sK2)) ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f35,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f918,plain,(
    v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    inference(resolution,[],[f912,f576])).

fof(f576,plain,(
    v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    inference(forward_demodulation,[],[f575,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f575,plain,(
    v4_pre_topc(k1_setfam_1(k2_tarski(sK2,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f543,f202])).

fof(f202,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f201,f28])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f201,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f200,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f200,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f199,f32])).

fof(f32,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f199,plain,
    ( ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f158,f34])).

fof(f34,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f158,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f36,f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

fof(f543,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | v4_pre_topc(k1_setfam_1(k2_tarski(sK2,sK1)),sK0) ),
    inference(resolution,[],[f469,f31])).

fof(f469,plain,(
    ! [X75] :
      ( ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X75,sK0)
      | v4_pre_topc(k1_setfam_1(k2_tarski(X75,sK1)),sK0) ) ),
    inference(forward_demodulation,[],[f468,f90])).

fof(f90,plain,(
    ! [X15] : k9_subset_1(u1_struct_0(sK0),X15,sK1) = k1_setfam_1(k2_tarski(X15,sK1)) ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f468,plain,(
    ! [X75] :
      ( ~ v4_pre_topc(X75,sK0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X75,sK1),sK0)
      | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f467,f28])).

fof(f467,plain,(
    ! [X75] :
      ( ~ v4_pre_topc(X75,sK0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X75,sK1),sK0)
      | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f466,f29])).

fof(f466,plain,(
    ! [X75] :
      ( ~ v4_pre_topc(X75,sK0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X75,sK1),sK0)
      | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f410,f198])).

fof(f198,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f197,f28])).

fof(f197,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f196,f29])).

fof(f196,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f195,f32])).

fof(f195,plain,
    ( ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f157,f33])).

fof(f33,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f157,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f36,f30])).

fof(f410,plain,(
    ! [X75] :
      ( ~ v4_pre_topc(sK1,sK0)
      | ~ v4_pre_topc(X75,sK0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X75,sK1),sK0)
      | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f37,f30])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

fof(f912,plain,(
    ! [X26] :
      ( ~ v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0)
      | v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0) ) ),
    inference(subsumption_resolution,[],[f911,f28])).

fof(f911,plain,(
    ! [X26] :
      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0)
      | ~ v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f910,f29])).

fof(f910,plain,(
    ! [X26] :
      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0)
      | ~ v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f909,f30])).

fof(f909,plain,(
    ! [X26] :
      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0)
      | ~ v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f870,f33])).

fof(f870,plain,(
    ! [X26] :
      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0)
      | ~ v2_compts_1(sK1,sK0)
      | ~ v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f293,f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f72,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f54,f62])).

fof(f62,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f44,f30])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f43,f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f293,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(u1_struct_0(X2)))
      | v2_compts_1(k1_setfam_1(k2_tarski(X0,X1)),X2)
      | ~ v2_compts_1(X0,X2)
      | ~ v4_pre_topc(k1_setfam_1(k2_tarski(X0,X1)),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X2,X0)
      | v2_compts_1(X2,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:35:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (22850)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (22841)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (22851)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (22850)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f922,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f918,f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ~v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.22/0.48    inference(backward_demodulation,[],[f35,f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X16] : (k9_subset_1(u1_struct_0(sK0),X16,sK2) = k1_setfam_1(k2_tarski(X16,sK2))) )),
% 0.22/0.48    inference(resolution,[],[f48,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f11])).
% 0.22/0.48  fof(f11,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f45,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f918,plain,(
% 0.22/0.48    v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.22/0.48    inference(resolution,[],[f912,f576])).
% 0.22/0.48  fof(f576,plain,(
% 0.22/0.48    v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.22/0.48    inference(forward_demodulation,[],[f575,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.48  fof(f575,plain,(
% 0.22/0.48    v4_pre_topc(k1_setfam_1(k2_tarski(sK2,sK1)),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f543,f202])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    v4_pre_topc(sK2,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f201,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    v4_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f200,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    v4_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f199,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    v8_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f199,plain,(
% 0.22/0.48    ~v8_pre_topc(sK0) | v4_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f158,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    v2_compts_1(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    ~v2_compts_1(sK2,sK0) | ~v8_pre_topc(sK0) | v4_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.48    inference(resolution,[],[f36,f31])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).
% 0.22/0.48  fof(f543,plain,(
% 0.22/0.48    ~v4_pre_topc(sK2,sK0) | v4_pre_topc(k1_setfam_1(k2_tarski(sK2,sK1)),sK0)),
% 0.22/0.48    inference(resolution,[],[f469,f31])).
% 0.22/0.48  fof(f469,plain,(
% 0.22/0.48    ( ! [X75] : (~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X75,sK0) | v4_pre_topc(k1_setfam_1(k2_tarski(X75,sK1)),sK0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f468,f90])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X15] : (k9_subset_1(u1_struct_0(sK0),X15,sK1) = k1_setfam_1(k2_tarski(X15,sK1))) )),
% 0.22/0.48    inference(resolution,[],[f48,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f468,plain,(
% 0.22/0.48    ( ! [X75] : (~v4_pre_topc(X75,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X75,sK1),sK0) | ~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f467,f28])).
% 0.22/0.48  fof(f467,plain,(
% 0.22/0.48    ( ! [X75] : (~v4_pre_topc(X75,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X75,sK1),sK0) | ~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f466,f29])).
% 0.22/0.48  fof(f466,plain,(
% 0.22/0.48    ( ! [X75] : (~v4_pre_topc(X75,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X75,sK1),sK0) | ~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f410,f198])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    v4_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f197,f28])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f196,f29])).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f195,f32])).
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    ~v8_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f157,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v2_compts_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    ~v2_compts_1(sK1,sK0) | ~v8_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.48    inference(resolution,[],[f36,f30])).
% 0.22/0.48  fof(f410,plain,(
% 0.22/0.48    ( ! [X75] : (~v4_pre_topc(sK1,sK0) | ~v4_pre_topc(X75,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X75,sK1),sK0) | ~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f37,f30])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).
% 0.22/0.48  fof(f912,plain,(
% 0.22/0.48    ( ! [X26] : (~v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0) | v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f911,f28])).
% 0.22/0.48  fof(f911,plain,(
% 0.22/0.48    ( ! [X26] : (v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0) | ~v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f910,f29])).
% 0.22/0.48  fof(f910,plain,(
% 0.22/0.48    ( ! [X26] : (v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0) | ~v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f909,f30])).
% 0.22/0.48  fof(f909,plain,(
% 0.22/0.48    ( ! [X26] : (v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0) | ~v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f870,f33])).
% 0.22/0.48  fof(f870,plain,(
% 0.22/0.48    ( ! [X26] : (v2_compts_1(k1_setfam_1(k2_tarski(sK1,X26)),sK0) | ~v2_compts_1(sK1,sK0) | ~v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X26)),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f293,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.48    inference(superposition,[],[f72,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f42,f41])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f54,f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 0.22/0.48    inference(resolution,[],[f44,f30])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.48    inference(resolution,[],[f43,f30])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.22/0.48  fof(f293,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(u1_struct_0(X2))) | v2_compts_1(k1_setfam_1(k2_tarski(X0,X1)),X2) | ~v2_compts_1(X0,X2) | ~v4_pre_topc(k1_setfam_1(k2_tarski(X0,X1)),X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) )),
% 0.22/0.48    inference(resolution,[],[f38,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f39,f41])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~v4_pre_topc(X2,X0) | v2_compts_1(X2,X0) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (22850)------------------------------
% 0.22/0.48  % (22850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22850)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (22850)Memory used [KB]: 2302
% 0.22/0.48  % (22850)Time elapsed: 0.027 s
% 0.22/0.48  % (22850)------------------------------
% 0.22/0.48  % (22850)------------------------------
% 0.22/0.48  % (22852)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (22833)Success in time 0.118 s
%------------------------------------------------------------------------------
