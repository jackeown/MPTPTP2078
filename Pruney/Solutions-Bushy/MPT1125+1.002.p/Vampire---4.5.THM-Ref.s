%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1125+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:18 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 971 expanded)
%              Number of leaves         :   24 ( 409 expanded)
%              Depth                    :   18
%              Number of atoms          :  540 (11818 expanded)
%              Number of equality atoms :   60 (1046 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2677,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2676,f2554])).

fof(f2554,plain,(
    ~ v4_pre_topc(k3_xboole_0(u1_struct_0(sK2),sK5(sK0,sK1,sK3)),sK2) ),
    inference(unit_resulting_resolution,[],[f161,f2532])).

fof(f2532,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k3_xboole_0(u1_struct_0(sK2),X0),sK2)
      | v4_pre_topc(k10_relat_1(sK3,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f2529,f412])).

fof(f412,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f203,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f203,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f199,f198])).

fof(f198,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)) = k3_xboole_0(X0,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f115,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f115,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f112,f113])).

fof(f113,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f98,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f98,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f54,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f54,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ v5_pre_topc(sK4,sK0,sK1)
    & sK3 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK2,sK1)
    & v5_pre_topc(sK3,sK0,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f42,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ v5_pre_topc(X4,X0,X1)
                        & X3 = X4
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X2,X1)
                    & v5_pre_topc(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & l1_pre_topc(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,sK0,X1)
                      & X3 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X2,X1)
                  & v5_pre_topc(X3,sK0,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v5_pre_topc(X4,sK0,X1)
                    & X3 = X4
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X2,X1)
                & v5_pre_topc(X3,sK0,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v5_pre_topc(X4,sK0,sK1)
                  & X3 = X4
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X2,sK1)
              & v5_pre_topc(X3,sK0,X2)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
              & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & l1_pre_topc(X2) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ v5_pre_topc(X4,sK0,sK1)
                & X3 = X4
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X2,sK1)
            & v5_pre_topc(X3,sK0,X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
            & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
            & v1_funct_1(X3) )
        & l1_pre_topc(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ v5_pre_topc(X4,sK0,sK1)
              & X3 = X4
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(sK2,sK1)
          & v5_pre_topc(X3,sK0,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
          & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2))
          & v1_funct_1(X3) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ v5_pre_topc(X4,sK0,sK1)
            & X3 = X4
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK2,sK1)
        & v5_pre_topc(X3,sK0,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
        & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ v5_pre_topc(X4,sK0,sK1)
          & sK3 = X4
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK2,sK1)
      & v5_pre_topc(sK3,sK0,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X4] :
        ( ~ v5_pre_topc(X4,sK0,sK1)
        & sK3 = X4
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ~ v5_pre_topc(sK4,sK0,sK1)
      & sK3 = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,X0,X1)
                      & X3 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X2,X1)
                  & v5_pre_topc(X3,X0,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,X0,X1)
                      & X3 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X2,X1)
                  & v5_pre_topc(X3,X0,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( l1_pre_topc(X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ( ( m1_pre_topc(X2,X1)
                        & v5_pre_topc(X3,X0,X2) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ( X3 = X4
                           => v5_pre_topc(X4,X0,X1) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ( ( m1_pre_topc(X2,X1)
                        & v5_pre_topc(X3,X0,X2) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ( X3 = X4
                           => v5_pre_topc(X4,X0,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ( ( m1_pre_topc(X2,X1)
                      & v5_pre_topc(X3,X0,X2) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( X3 = X4
                         => v5_pre_topc(X4,X0,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_pre_topc)).

fof(f112,plain,(
    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f98,f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f199,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f115,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f2529,plain,(
    ! [X0] :
      ( v4_pre_topc(k10_relat_1(sK3,X0),sK0)
      | ~ m1_subset_1(k3_xboole_0(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(k3_xboole_0(u1_struct_0(sK2),X0),sK2) ) ),
    inference(superposition,[],[f497,f2509])).

fof(f2509,plain,(
    ! [X0] : k10_relat_1(sK3,X0) = k10_relat_1(sK3,k3_xboole_0(u1_struct_0(sK2),X0)) ),
    inference(forward_demodulation,[],[f2431,f136])).

fof(f136,plain,(
    ! [X0] : k10_relat_1(sK3,X0) = k10_relat_1(sK3,k3_xboole_0(k2_relat_1(sK3),X0)) ),
    inference(unit_resulting_resolution,[],[f125,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f125,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f57,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f2431,plain,(
    ! [X0] : k10_relat_1(sK3,k3_xboole_0(k2_relat_1(sK3),X0)) = k10_relat_1(sK3,k3_xboole_0(u1_struct_0(sK2),X0)) ),
    inference(superposition,[],[f136,f359])).

fof(f359,plain,(
    ! [X0] : k3_xboole_0(k2_relat_1(sK3),X0) = k3_xboole_0(k2_relat_1(sK3),k3_xboole_0(u1_struct_0(sK2),X0)) ),
    inference(superposition,[],[f80,f162])).

fof(f162,plain,(
    k2_relat_1(sK3) = k3_xboole_0(k2_relat_1(sK3),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f140,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f140,plain,(
    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f135,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f135,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f123,f124])).

fof(f124,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f57,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f123,plain,(
    m1_subset_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f57,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f80,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f497,plain,(
    ! [X0] :
      ( v4_pre_topc(k10_relat_1(sK3,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X0,sK2) ) ),
    inference(forward_demodulation,[],[f496,f122])).

fof(f122,plain,(
    ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f57,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f496,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X0,sK2)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f495,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f495,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X0,sK2)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f494,f54])).

fof(f494,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X0,sK2)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f493,f56])).

fof(f56,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f493,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X0,sK2)
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f491,f58])).

fof(f58,plain,(
    v5_pre_topc(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f491,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v5_pre_topc(sK3,sK0,sK2)
      | ~ v4_pre_topc(X0,sK2)
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f101,f57])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(sK3,X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v1_funct_2(sK3,u1_struct_0(X2),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK3,X0),X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f91,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
                    & v4_pre_topc(sK5(X0,X1,X2),X1)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
        & v4_pre_topc(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f91,plain,(
    v1_funct_1(sK3) ),
    inference(forward_demodulation,[],[f60,f63])).

fof(f63,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f161,plain,(
    ~ v4_pre_topc(k10_relat_1(sK3,sK5(sK0,sK1,sK3)),sK0) ),
    inference(forward_demodulation,[],[f146,f147])).

fof(f147,plain,(
    ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f89,f86])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f62,f63])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f146,plain,(
    ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK5(sK0,sK1,sK3)),sK0) ),
    inference(unit_resulting_resolution,[],[f52,f53,f91,f88,f90,f89,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f61,f63])).

fof(f61,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ~ v5_pre_topc(sK3,sK0,sK1) ),
    inference(backward_demodulation,[],[f64,f63])).

fof(f64,plain,(
    ~ v5_pre_topc(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f2676,plain,(
    v4_pre_topc(k3_xboole_0(u1_struct_0(sK2),sK5(sK0,sK1,sK3)),sK2) ),
    inference(forward_demodulation,[],[f2674,f76])).

fof(f2674,plain,(
    v4_pre_topc(k3_xboole_0(sK5(sK0,sK1,sK3),u1_struct_0(sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f53,f59,f145,f144,f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v4_pre_topc(k3_xboole_0(X0,u1_struct_0(sK2)),sK2)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f205,f203])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_xboole_0(X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(k3_xboole_0(X0,u1_struct_0(sK2)),sK2)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f204,f198])).

fof(f204,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X0,u1_struct_0(sK2)),sK2)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(backward_demodulation,[],[f120,f198])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),sK2)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f87,f113])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK6(X0,X1,X2),X0)
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f144,plain,(
    m1_subset_1(sK5(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f52,f53,f91,f88,f90,f89,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f145,plain,(
    v4_pre_topc(sK5(sK0,sK1,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f52,f53,f91,f88,f90,f89,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | v4_pre_topc(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

%------------------------------------------------------------------------------
