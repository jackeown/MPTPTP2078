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
% DateTime   : Thu Dec  3 13:12:19 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 885 expanded)
%              Number of leaves         :   16 ( 296 expanded)
%              Depth                    :   21
%              Number of atoms          :  359 (4186 expanded)
%              Number of equality atoms :   90 ( 873 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1051,f1137])).

fof(f1137,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f1136])).

fof(f1136,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f1135,f77])).

fof(f77,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) ),
    inference(backward_demodulation,[],[f74,f71])).

fof(f71,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(resolution,[],[f55,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f48,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f74,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) ),
    inference(backward_demodulation,[],[f68,f73])).

fof(f73,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,sK1) = k1_setfam_1(k2_tarski(X3,sK1)) ),
    inference(resolution,[],[f55,f70])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f34,f67])).

fof(f67,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f66,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    & v3_pre_topc(sK2,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
              & v3_pre_topc(X2,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v1_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
            & v3_pre_topc(X2,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v1_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
          & v3_pre_topc(X2,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
        & v3_pre_topc(X2,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
      & v3_pre_topc(sK2,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
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
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    inference(backward_demodulation,[],[f38,f67])).

fof(f38,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f1135,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1))
    | spl4_8 ),
    inference(forward_demodulation,[],[f1052,f1087])).

fof(f1087,plain,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))
    | spl4_8 ),
    inference(superposition,[],[f1083,f71])).

fof(f1083,plain,
    ( sK2 = k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))
    | spl4_8 ),
    inference(resolution,[],[f547,f122])).

fof(f122,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(X4,X5,X4),X4)
      | k9_subset_1(X5,X4,X5) = X4 ) ),
    inference(superposition,[],[f120,f71])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | r2_hidden(sK3(X0,X1,X0),X0) ) ),
    inference(factoring,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f52,f46])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f547,plain,
    ( ~ r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl4_8
  <=> r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1052,plain,(
    k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f1047,f76])).

fof(f76,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(sK1,X3,sK1) ),
    inference(backward_demodulation,[],[f73,f71])).

fof(f1047,plain,(
    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f1046,f71])).

fof(f1046,plain,(
    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1044,f70])).

fof(f1044,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f428,f85])).

fof(f85,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f84,f70])).

fof(f84,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f83,f35])).

fof(f35,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f82,f67])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ) ),
    inference(resolution,[],[f43,f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f428,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f427,f69])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f36,f67])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f427,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) ),
    inference(resolution,[],[f306,f37])).

fof(f37,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f305,f67])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f304,f67])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f303,f67])).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(subsumption_resolution,[],[f302,f33])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
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
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

fof(f1051,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f1050])).

fof(f1050,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f1049,f77])).

fof(f1049,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1))
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f1048,f76])).

fof(f1048,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f1047,f561])).

fof(f561,plain,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f560,f343])).

fof(f343,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK2,X2,sK2),k2_struct_0(sK0))
      | sK2 = k1_setfam_1(k2_tarski(sK2,X2)) ) ),
    inference(resolution,[],[f199,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f199,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK2,X2,sK2),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))
      | sK2 = k1_setfam_1(k2_tarski(sK2,X2)) ) ),
    inference(superposition,[],[f196,f71])).

fof(f196,plain,(
    ! [X3] :
      ( sK2 = k9_subset_1(X3,sK2,X3)
      | r2_hidden(sK3(sK2,X3,sK2),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X3] :
      ( r2_hidden(sK3(sK2,X3,sK2),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))
      | sK2 = k9_subset_1(X3,sK2,X3)
      | sK2 = k9_subset_1(X3,sK2,X3) ) ),
    inference(resolution,[],[f151,f122])).

fof(f151,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK3(sK2,X4,sK2),X5)
      | r2_hidden(sK3(sK2,X4,sK2),k1_setfam_1(k2_tarski(X5,k2_struct_0(sK0))))
      | sK2 = k9_subset_1(X4,sK2,X4) ) ),
    inference(resolution,[],[f147,f62])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f147,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK2,X2,sK2),k2_struct_0(sK0))
      | sK2 = k9_subset_1(X2,sK2,X2) ) ),
    inference(resolution,[],[f131,f69])).

fof(f131,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | r2_hidden(sK3(X13,X12,X13),X14)
      | k9_subset_1(X12,X13,X12) = X13 ) ),
    inference(resolution,[],[f122,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f560,plain,
    ( ~ r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0))
    | sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f554,f548])).

fof(f548,plain,
    ( r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f546])).

fof(f554,plain,
    ( ~ r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0))
    | ~ r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),sK2)
    | sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(resolution,[],[f548,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f54,f46])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:28:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (5961)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.17/0.51  % (5943)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.17/0.51  % (5936)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.17/0.52  % (5943)Refutation not found, incomplete strategy% (5943)------------------------------
% 1.17/0.52  % (5943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (5943)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.52  
% 1.17/0.52  % (5943)Memory used [KB]: 10746
% 1.17/0.52  % (5943)Time elapsed: 0.108 s
% 1.17/0.52  % (5943)------------------------------
% 1.17/0.52  % (5943)------------------------------
% 1.33/0.53  % (5934)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.53  % (5941)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.54  % (5937)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.54  % (5935)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (5946)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.54  % (5944)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (5935)Refutation not found, incomplete strategy% (5935)------------------------------
% 1.33/0.54  % (5935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (5935)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (5935)Memory used [KB]: 10874
% 1.33/0.54  % (5935)Time elapsed: 0.127 s
% 1.33/0.54  % (5935)------------------------------
% 1.33/0.54  % (5935)------------------------------
% 1.33/0.54  % (5960)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.54  % (5962)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.54  % (5951)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.54  % (5958)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.55  % (5940)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.55  % (5952)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.55  % (5945)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.55  % (5963)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.55  % (5959)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.55  % (5950)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.55  % (5941)Refutation not found, incomplete strategy% (5941)------------------------------
% 1.33/0.55  % (5941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (5941)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (5941)Memory used [KB]: 10746
% 1.33/0.55  % (5941)Time elapsed: 0.137 s
% 1.33/0.55  % (5941)------------------------------
% 1.33/0.55  % (5941)------------------------------
% 1.33/0.55  % (5938)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.55  % (5957)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.55  % (5953)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.55  % (5942)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.56  % (5954)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.56  % (5939)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.56  % (5944)Refutation not found, incomplete strategy% (5944)------------------------------
% 1.33/0.56  % (5944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (5944)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (5949)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.56  % (5944)Memory used [KB]: 10746
% 1.33/0.56  % (5944)Time elapsed: 0.129 s
% 1.33/0.56  % (5944)------------------------------
% 1.33/0.56  % (5944)------------------------------
% 1.33/0.56  % (5933)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.56  % (5947)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.56  % (5954)Refutation not found, incomplete strategy% (5954)------------------------------
% 1.33/0.56  % (5954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (5954)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (5954)Memory used [KB]: 10874
% 1.33/0.56  % (5954)Time elapsed: 0.152 s
% 1.33/0.56  % (5954)------------------------------
% 1.33/0.56  % (5954)------------------------------
% 1.33/0.56  % (5956)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.57  % (5951)Refutation not found, incomplete strategy% (5951)------------------------------
% 1.33/0.57  % (5951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.57  % (5951)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.57  
% 1.33/0.57  % (5951)Memory used [KB]: 10618
% 1.33/0.57  % (5951)Time elapsed: 0.150 s
% 1.33/0.57  % (5951)------------------------------
% 1.33/0.57  % (5951)------------------------------
% 1.33/0.57  % (5955)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.57  % (5955)Refutation not found, incomplete strategy% (5955)------------------------------
% 1.33/0.57  % (5955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.57  % (5955)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.57  
% 1.33/0.57  % (5955)Memory used [KB]: 1791
% 1.33/0.57  % (5955)Time elapsed: 0.160 s
% 1.33/0.57  % (5955)------------------------------
% 1.33/0.57  % (5955)------------------------------
% 1.33/0.58  % (5942)Refutation not found, incomplete strategy% (5942)------------------------------
% 1.33/0.58  % (5942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.58  % (5942)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.58  
% 1.33/0.58  % (5942)Memory used [KB]: 10874
% 1.33/0.58  % (5942)Time elapsed: 0.163 s
% 1.33/0.58  % (5942)------------------------------
% 1.33/0.58  % (5942)------------------------------
% 1.33/0.59  % (5933)Refutation not found, incomplete strategy% (5933)------------------------------
% 1.33/0.59  % (5933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.59  % (5933)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.59  
% 1.33/0.59  % (5933)Memory used [KB]: 1918
% 1.33/0.59  % (5933)Time elapsed: 0.148 s
% 1.33/0.59  % (5933)------------------------------
% 1.33/0.59  % (5933)------------------------------
% 1.33/0.59  % (5956)Refutation not found, incomplete strategy% (5956)------------------------------
% 1.33/0.59  % (5956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.59  % (5956)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.59  
% 1.33/0.59  % (5956)Memory used [KB]: 10746
% 1.33/0.59  % (5956)Time elapsed: 0.109 s
% 1.33/0.59  % (5956)------------------------------
% 1.33/0.59  % (5956)------------------------------
% 1.97/0.63  % (5936)Refutation found. Thanks to Tanya!
% 1.97/0.63  % SZS status Theorem for theBenchmark
% 1.97/0.63  % SZS output start Proof for theBenchmark
% 1.97/0.63  fof(f1138,plain,(
% 1.97/0.63    $false),
% 1.97/0.63    inference(avatar_sat_refutation,[],[f1051,f1137])).
% 1.97/0.63  fof(f1137,plain,(
% 1.97/0.63    spl4_8),
% 1.97/0.63    inference(avatar_contradiction_clause,[],[f1136])).
% 1.97/0.63  fof(f1136,plain,(
% 1.97/0.63    $false | spl4_8),
% 1.97/0.63    inference(subsumption_resolution,[],[f1135,f77])).
% 1.97/0.63  fof(f77,plain,(
% 1.97/0.63    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1))),
% 1.97/0.63    inference(backward_demodulation,[],[f74,f71])).
% 1.97/0.63  fof(f71,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.97/0.63    inference(resolution,[],[f55,f65])).
% 1.97/0.63  fof(f65,plain,(
% 1.97/0.63    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.97/0.63    inference(forward_demodulation,[],[f40,f39])).
% 1.97/0.63  fof(f39,plain,(
% 1.97/0.63    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.97/0.63    inference(cnf_transformation,[],[f2])).
% 1.97/0.63  fof(f2,axiom,(
% 1.97/0.63    ! [X0] : k2_subset_1(X0) = X0),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.97/0.63  fof(f40,plain,(
% 1.97/0.63    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f3])).
% 1.97/0.63  fof(f3,axiom,(
% 1.97/0.63    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.97/0.63  fof(f55,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.97/0.63    inference(definition_unfolding,[],[f48,f46])).
% 1.97/0.63  fof(f46,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f6])).
% 1.97/0.63  fof(f6,axiom,(
% 1.97/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.97/0.63  fof(f48,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f21])).
% 1.97/0.63  fof(f21,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.97/0.63    inference(ennf_transformation,[],[f5])).
% 1.97/0.63  fof(f5,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.97/0.63  fof(f74,plain,(
% 1.97/0.63    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1)))),
% 1.97/0.63    inference(backward_demodulation,[],[f68,f73])).
% 1.97/0.63  fof(f73,plain,(
% 1.97/0.63    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,sK1) = k1_setfam_1(k2_tarski(X3,sK1))) )),
% 1.97/0.63    inference(resolution,[],[f55,f70])).
% 1.97/0.63  fof(f70,plain,(
% 1.97/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.97/0.63    inference(backward_demodulation,[],[f34,f67])).
% 1.97/0.63  fof(f67,plain,(
% 1.97/0.63    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.97/0.63    inference(resolution,[],[f66,f33])).
% 1.97/0.63  fof(f33,plain,(
% 1.97/0.63    l1_pre_topc(sK0)),
% 1.97/0.63    inference(cnf_transformation,[],[f25])).
% 1.97/0.63  fof(f25,plain,(
% 1.97/0.63    ((k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.97/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24,f23,f22])).
% 1.97/0.63  fof(f22,plain,(
% 1.97/0.63    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f23,plain,(
% 1.97/0.63    ? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f24,plain,(
% 1.97/0.63    ? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f14,plain,(
% 1.97/0.63    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.97/0.63    inference(flattening,[],[f13])).
% 1.97/0.63  fof(f13,plain,(
% 1.97/0.63    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.97/0.63    inference(ennf_transformation,[],[f12])).
% 1.97/0.63  fof(f12,negated_conjecture,(
% 1.97/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.97/0.63    inference(negated_conjecture,[],[f11])).
% 1.97/0.63  fof(f11,conjecture,(
% 1.97/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).
% 1.97/0.63  fof(f66,plain,(
% 1.97/0.63    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.97/0.63    inference(resolution,[],[f41,f42])).
% 1.97/0.63  fof(f42,plain,(
% 1.97/0.63    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f16])).
% 1.97/0.63  fof(f16,plain,(
% 1.97/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.97/0.63    inference(ennf_transformation,[],[f8])).
% 1.97/0.63  fof(f8,axiom,(
% 1.97/0.63    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.97/0.63  fof(f41,plain,(
% 1.97/0.63    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f15])).
% 1.97/0.63  fof(f15,plain,(
% 1.97/0.63    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.97/0.63    inference(ennf_transformation,[],[f7])).
% 1.97/0.63  fof(f7,axiom,(
% 1.97/0.63    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.97/0.63  fof(f34,plain,(
% 1.97/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.97/0.63    inference(cnf_transformation,[],[f25])).
% 1.97/0.63  fof(f68,plain,(
% 1.97/0.63    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 1.97/0.63    inference(backward_demodulation,[],[f38,f67])).
% 1.97/0.63  fof(f38,plain,(
% 1.97/0.63    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 1.97/0.63    inference(cnf_transformation,[],[f25])).
% 1.97/0.63  fof(f1135,plain,(
% 1.97/0.63    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) | spl4_8),
% 1.97/0.63    inference(forward_demodulation,[],[f1052,f1087])).
% 1.97/0.63  fof(f1087,plain,(
% 1.97/0.63    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) | spl4_8),
% 1.97/0.63    inference(superposition,[],[f1083,f71])).
% 1.97/0.63  fof(f1083,plain,(
% 1.97/0.63    sK2 = k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)) | spl4_8),
% 1.97/0.63    inference(resolution,[],[f547,f122])).
% 1.97/0.63  fof(f122,plain,(
% 1.97/0.63    ( ! [X4,X5] : (r2_hidden(sK3(X4,X5,X4),X4) | k9_subset_1(X5,X4,X5) = X4) )),
% 1.97/0.63    inference(superposition,[],[f120,f71])).
% 1.97/0.63  fof(f120,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | r2_hidden(sK3(X0,X1,X0),X0)) )),
% 1.97/0.63    inference(factoring,[],[f58])).
% 1.97/0.63  fof(f58,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.97/0.63    inference(definition_unfolding,[],[f52,f46])).
% 1.97/0.63  fof(f52,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f31])).
% 1.97/0.63  fof(f31,plain,(
% 1.97/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.97/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.97/0.63  fof(f30,plain,(
% 1.97/0.63    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f29,plain,(
% 1.97/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.97/0.63    inference(rectify,[],[f28])).
% 1.97/0.63  fof(f28,plain,(
% 1.97/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.97/0.63    inference(flattening,[],[f27])).
% 1.97/0.63  fof(f27,plain,(
% 1.97/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.97/0.63    inference(nnf_transformation,[],[f1])).
% 1.97/0.63  fof(f1,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.97/0.63  fof(f547,plain,(
% 1.97/0.63    ~r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),sK2) | spl4_8),
% 1.97/0.63    inference(avatar_component_clause,[],[f546])).
% 1.97/0.63  fof(f546,plain,(
% 1.97/0.63    spl4_8 <=> r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),sK2)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.97/0.63  fof(f1052,plain,(
% 1.97/0.63    k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))),
% 1.97/0.63    inference(forward_demodulation,[],[f1047,f76])).
% 1.97/0.63  fof(f76,plain,(
% 1.97/0.63    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(sK1,X3,sK1)) )),
% 1.97/0.63    inference(backward_demodulation,[],[f73,f71])).
% 1.97/0.63  fof(f1047,plain,(
% 1.97/0.63    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))),
% 1.97/0.63    inference(forward_demodulation,[],[f1046,f71])).
% 1.97/0.63  fof(f1046,plain,(
% 1.97/0.63    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))),
% 1.97/0.63    inference(subsumption_resolution,[],[f1044,f70])).
% 1.97/0.63  fof(f1044,plain,(
% 1.97/0.63    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.97/0.63    inference(superposition,[],[f428,f85])).
% 1.97/0.63  fof(f85,plain,(
% 1.97/0.63    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.97/0.63    inference(subsumption_resolution,[],[f84,f70])).
% 1.97/0.63  fof(f84,plain,(
% 1.97/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.97/0.63    inference(resolution,[],[f83,f35])).
% 1.97/0.63  fof(f35,plain,(
% 1.97/0.63    v1_tops_1(sK1,sK0)),
% 1.97/0.63    inference(cnf_transformation,[],[f25])).
% 1.97/0.63  fof(f83,plain,(
% 1.97/0.63    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)) )),
% 1.97/0.63    inference(forward_demodulation,[],[f82,f67])).
% 1.97/0.63  fof(f82,plain,(
% 1.97/0.63    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)) )),
% 1.97/0.63    inference(resolution,[],[f43,f33])).
% 1.97/0.63  fof(f43,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f26])).
% 1.97/0.63  fof(f26,plain,(
% 1.97/0.63    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.97/0.63    inference(nnf_transformation,[],[f17])).
% 1.97/0.63  fof(f17,plain,(
% 1.97/0.63    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.97/0.63    inference(ennf_transformation,[],[f9])).
% 1.97/0.63  fof(f9,axiom,(
% 1.97/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 1.97/0.63  fof(f428,plain,(
% 1.97/0.63    ( ! [X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f427,f69])).
% 1.97/0.63  fof(f69,plain,(
% 1.97/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.97/0.63    inference(backward_demodulation,[],[f36,f67])).
% 1.97/0.63  fof(f36,plain,(
% 1.97/0.63    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.97/0.63    inference(cnf_transformation,[],[f25])).
% 1.97/0.63  fof(f427,plain,(
% 1.97/0.63    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))) )),
% 1.97/0.63    inference(resolution,[],[f306,f37])).
% 1.97/0.63  fof(f37,plain,(
% 1.97/0.63    v3_pre_topc(sK2,sK0)),
% 1.97/0.63    inference(cnf_transformation,[],[f25])).
% 1.97/0.63  fof(f306,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))) )),
% 1.97/0.63    inference(forward_demodulation,[],[f305,f67])).
% 1.97/0.63  fof(f305,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.97/0.63    inference(forward_demodulation,[],[f304,f67])).
% 1.97/0.63  fof(f304,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.97/0.63    inference(forward_demodulation,[],[f303,f67])).
% 1.97/0.63  fof(f303,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f302,f33])).
% 1.97/0.63  fof(f302,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.97/0.63    inference(resolution,[],[f45,f32])).
% 1.97/0.63  fof(f32,plain,(
% 1.97/0.63    v2_pre_topc(sK0)),
% 1.97/0.63    inference(cnf_transformation,[],[f25])).
% 1.97/0.63  fof(f45,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f19])).
% 1.97/0.63  fof(f19,plain,(
% 1.97/0.63    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.97/0.63    inference(flattening,[],[f18])).
% 1.97/0.63  fof(f18,plain,(
% 1.97/0.63    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.97/0.63    inference(ennf_transformation,[],[f10])).
% 1.97/0.63  fof(f10,axiom,(
% 1.97/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
% 1.97/0.63  fof(f1051,plain,(
% 1.97/0.63    ~spl4_8),
% 1.97/0.63    inference(avatar_contradiction_clause,[],[f1050])).
% 1.97/0.63  fof(f1050,plain,(
% 1.97/0.63    $false | ~spl4_8),
% 1.97/0.63    inference(subsumption_resolution,[],[f1049,f77])).
% 1.97/0.63  fof(f1049,plain,(
% 1.97/0.63    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) | ~spl4_8),
% 1.97/0.63    inference(forward_demodulation,[],[f1048,f76])).
% 1.97/0.63  fof(f1048,plain,(
% 1.97/0.63    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | ~spl4_8),
% 1.97/0.63    inference(forward_demodulation,[],[f1047,f561])).
% 1.97/0.63  fof(f561,plain,(
% 1.97/0.63    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) | ~spl4_8),
% 1.97/0.63    inference(subsumption_resolution,[],[f560,f343])).
% 1.97/0.63  fof(f343,plain,(
% 1.97/0.63    ( ! [X2] : (r2_hidden(sK3(sK2,X2,sK2),k2_struct_0(sK0)) | sK2 = k1_setfam_1(k2_tarski(sK2,X2))) )),
% 1.97/0.63    inference(resolution,[],[f199,f63])).
% 1.97/0.63  fof(f63,plain,(
% 1.97/0.63    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | r2_hidden(X4,X1)) )),
% 1.97/0.63    inference(equality_resolution,[],[f60])).
% 1.97/0.63  fof(f60,plain,(
% 1.97/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.97/0.63    inference(definition_unfolding,[],[f50,f46])).
% 1.97/0.63  fof(f50,plain,(
% 1.97/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.97/0.63    inference(cnf_transformation,[],[f31])).
% 1.97/0.63  fof(f199,plain,(
% 1.97/0.63    ( ! [X2] : (r2_hidden(sK3(sK2,X2,sK2),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) | sK2 = k1_setfam_1(k2_tarski(sK2,X2))) )),
% 1.97/0.63    inference(superposition,[],[f196,f71])).
% 1.97/0.63  fof(f196,plain,(
% 1.97/0.63    ( ! [X3] : (sK2 = k9_subset_1(X3,sK2,X3) | r2_hidden(sK3(sK2,X3,sK2),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))) )),
% 1.97/0.63    inference(duplicate_literal_removal,[],[f194])).
% 1.97/0.63  fof(f194,plain,(
% 1.97/0.63    ( ! [X3] : (r2_hidden(sK3(sK2,X3,sK2),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) | sK2 = k9_subset_1(X3,sK2,X3) | sK2 = k9_subset_1(X3,sK2,X3)) )),
% 1.97/0.63    inference(resolution,[],[f151,f122])).
% 1.97/0.63  fof(f151,plain,(
% 1.97/0.63    ( ! [X4,X5] : (~r2_hidden(sK3(sK2,X4,sK2),X5) | r2_hidden(sK3(sK2,X4,sK2),k1_setfam_1(k2_tarski(X5,k2_struct_0(sK0)))) | sK2 = k9_subset_1(X4,sK2,X4)) )),
% 1.97/0.63    inference(resolution,[],[f147,f62])).
% 1.97/0.63  fof(f62,plain,(
% 1.97/0.63    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X0)) )),
% 1.97/0.63    inference(equality_resolution,[],[f59])).
% 1.97/0.63  fof(f59,plain,(
% 1.97/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.97/0.63    inference(definition_unfolding,[],[f51,f46])).
% 1.97/0.63  fof(f51,plain,(
% 1.97/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.97/0.63    inference(cnf_transformation,[],[f31])).
% 1.97/0.63  fof(f147,plain,(
% 1.97/0.63    ( ! [X2] : (r2_hidden(sK3(sK2,X2,sK2),k2_struct_0(sK0)) | sK2 = k9_subset_1(X2,sK2,X2)) )),
% 1.97/0.63    inference(resolution,[],[f131,f69])).
% 1.97/0.63  fof(f131,plain,(
% 1.97/0.63    ( ! [X14,X12,X13] : (~m1_subset_1(X13,k1_zfmisc_1(X14)) | r2_hidden(sK3(X13,X12,X13),X14) | k9_subset_1(X12,X13,X12) = X13) )),
% 1.97/0.63    inference(resolution,[],[f122,f47])).
% 1.97/0.63  fof(f47,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f20])).
% 1.97/0.63  fof(f20,plain,(
% 1.97/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.97/0.63    inference(ennf_transformation,[],[f4])).
% 1.97/0.63  fof(f4,axiom,(
% 1.97/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.97/0.63  fof(f560,plain,(
% 1.97/0.63    ~r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0)) | sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) | ~spl4_8),
% 1.97/0.63    inference(subsumption_resolution,[],[f554,f548])).
% 1.97/0.63  fof(f548,plain,(
% 1.97/0.63    r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),sK2) | ~spl4_8),
% 1.97/0.63    inference(avatar_component_clause,[],[f546])).
% 1.97/0.63  fof(f554,plain,(
% 1.97/0.63    ~r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0)) | ~r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),sK2) | sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) | ~spl4_8),
% 1.97/0.63    inference(resolution,[],[f548,f56])).
% 1.97/0.63  fof(f56,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.97/0.63    inference(definition_unfolding,[],[f54,f46])).
% 1.97/0.63  fof(f54,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f31])).
% 1.97/0.63  % SZS output end Proof for theBenchmark
% 1.97/0.63  % (5936)------------------------------
% 1.97/0.63  % (5936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (5936)Termination reason: Refutation
% 1.97/0.63  
% 1.97/0.63  % (5936)Memory used [KB]: 11513
% 1.97/0.63  % (5936)Time elapsed: 0.190 s
% 1.97/0.63  % (5936)------------------------------
% 1.97/0.63  % (5936)------------------------------
% 1.97/0.63  % (5931)Success in time 0.267 s
%------------------------------------------------------------------------------
