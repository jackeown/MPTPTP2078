%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t56_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:44 EDT 2019

% Result     : Theorem 3.26s
% Output     : Refutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 950 expanded)
%              Number of leaves         :   23 ( 417 expanded)
%              Depth                    :   22
%              Number of atoms          :  613 (12571 expanded)
%              Number of equality atoms :   55 (1002 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12778,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12777,f3083])).

fof(f3083,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(u1_struct_0(sK2),X1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f957,f139])).

fof(f139,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',commutativity_k3_xboole_0)).

fof(f957,plain,(
    ! [X7] : m1_subset_1(k3_xboole_0(X7,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f943,f942])).

fof(f942,plain,(
    ! [X7] : m1_subset_1(k9_subset_1(u1_struct_0(sK2),X7,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f318,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',dt_k9_subset_1)).

fof(f318,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f317,f316])).

fof(f316,plain,(
    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f202,f125])).

fof(f125,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',dt_k2_struct_0)).

fof(f202,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f111,f126])).

fof(f126,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',dt_l1_pre_topc)).

fof(f111,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,
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
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f50,f86,f85,f84,f83,f82])).

fof(f82,plain,
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
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
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
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
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
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v5_pre_topc(X4,X0,sK1)
                    & X3 = X4
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X2,sK1)
                & v5_pre_topc(X3,X0,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1] :
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
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ v5_pre_topc(X4,X0,X1)
                & X3 = X4
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(sK2,X1)
            & v5_pre_topc(X3,X0,sK2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X3) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X2,X0,X1] :
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
     => ( ? [X4] :
            ( ~ v5_pre_topc(X4,X0,X1)
            & sK3 = X4
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X2,X1)
        & v5_pre_topc(sK3,X0,X2)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ? [X4] :
          ( ~ v5_pre_topc(X4,X0,X1)
          & X3 = X4
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ~ v5_pre_topc(sK4,X0,X1)
        & sK4 = X3
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',t56_pre_topc)).

fof(f317,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f202,f124])).

fof(f124,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',d3_struct_0)).

fof(f943,plain,(
    ! [X8] : k3_xboole_0(X8,u1_struct_0(sK2)) = k9_subset_1(u1_struct_0(sK2),X8,u1_struct_0(sK2)) ),
    inference(resolution,[],[f318,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',redefinition_k9_subset_1)).

fof(f12777,plain,(
    ~ m1_subset_1(k3_xboole_0(u1_struct_0(sK2),sK5(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f12735,f312])).

fof(f312,plain,(
    ~ v4_pre_topc(k10_relat_1(sK3,sK5(sK0,sK1,sK3)),sK0) ),
    inference(backward_demodulation,[],[f302,f256])).

fof(f256,plain,(
    ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK5(sK0,sK1,sK3)),sK0) ),
    inference(subsumption_resolution,[],[f255,f107])).

fof(f107,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f255,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK5(sK0,sK1,sK3)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f254,f109])).

fof(f109,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

fof(f254,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK5(sK0,sK1,sK3)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f253,f171])).

fof(f171,plain,(
    v1_funct_1(sK3) ),
    inference(forward_demodulation,[],[f117,f120])).

fof(f120,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f87])).

fof(f117,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

fof(f253,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK5(sK0,sK1,sK3)),sK0)
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f252,f170])).

fof(f170,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f118,f120])).

fof(f118,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f252,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK5(sK0,sK1,sK3)),sK0)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f241,f169])).

fof(f169,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f119,f120])).

fof(f119,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

fof(f241,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK5(sK0,sK1,sK3)),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f168,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f89,f90])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
        & v4_pre_topc(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
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
    inference(rectify,[],[f88])).

fof(f88,plain,(
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
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',d12_pre_topc)).

fof(f168,plain,(
    ~ v5_pre_topc(sK3,sK0,sK1) ),
    inference(backward_demodulation,[],[f120,f121])).

fof(f121,plain,(
    ~ v5_pre_topc(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f87])).

fof(f302,plain,(
    ! [X2] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X2) = k10_relat_1(sK3,X2) ),
    inference(resolution,[],[f169,f164])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',redefinition_k8_relset_1)).

fof(f12735,plain,
    ( v4_pre_topc(k10_relat_1(sK3,sK5(sK0,sK1,sK3)),sK0)
    | ~ m1_subset_1(k3_xboole_0(u1_struct_0(sK2),sK5(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f12732,f1401])).

fof(f1401,plain,
    ( ~ m1_subset_1(k3_xboole_0(u1_struct_0(sK2),sK5(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k10_relat_1(sK3,k3_xboole_0(u1_struct_0(sK2),sK5(sK0,sK1,sK3))),sK0) ),
    inference(resolution,[],[f986,f289])).

fof(f289,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK2)
      | v4_pre_topc(k10_relat_1(sK3,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(backward_demodulation,[],[f278,f238])).

fof(f238,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f237,f107])).

fof(f237,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f236,f111])).

fof(f236,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f235,f171])).

fof(f235,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f113])).

fof(f113,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

fof(f234,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f114])).

fof(f114,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f87])).

fof(f233,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0),sK0)
      | ~ v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f115,f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f115,plain,(
    v5_pre_topc(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f87])).

fof(f278,plain,(
    ! [X2] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X2) = k10_relat_1(sK3,X2) ),
    inference(resolution,[],[f114,f164])).

fof(f986,plain,(
    v4_pre_topc(k3_xboole_0(u1_struct_0(sK2),sK5(sK0,sK1,sK3)),sK2) ),
    inference(subsumption_resolution,[],[f985,f957])).

fof(f985,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK5(sK0,sK1,sK3),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k3_xboole_0(u1_struct_0(sK2),sK5(sK0,sK1,sK3)),sK2) ),
    inference(forward_demodulation,[],[f984,f943])).

fof(f984,plain,
    ( v4_pre_topc(k3_xboole_0(u1_struct_0(sK2),sK5(sK0,sK1,sK3)),sK2)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK5(sK0,sK1,sK3),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f960,f139])).

fof(f960,plain,
    ( v4_pre_topc(k3_xboole_0(sK5(sK0,sK1,sK3),u1_struct_0(sK2)),sK2)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK5(sK0,sK1,sK3),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f943,f827])).

fof(f827,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK5(sK0,sK1,sK3),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK5(sK0,sK1,sK3),u1_struct_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f818,f246])).

fof(f246,plain,(
    m1_subset_1(sK5(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f245,f107])).

fof(f245,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f244,f109])).

fof(f244,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f243,f171])).

fof(f243,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f242,f170])).

fof(f242,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f239,f169])).

fof(f239,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f168,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f818,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK5(sK0,sK1,sK3),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK5(sK0,sK1,sK3),u1_struct_0(sK2)),sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f321,f251])).

fof(f251,plain,(
    v4_pre_topc(sK5(sK0,sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f250,f107])).

fof(f250,plain,
    ( v4_pre_topc(sK5(sK0,sK1,sK3),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f249,f109])).

fof(f249,plain,
    ( v4_pre_topc(sK5(sK0,sK1,sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f248,f171])).

fof(f248,plain,
    ( v4_pre_topc(sK5(sK0,sK1,sK3),sK1)
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f247,f170])).

fof(f247,plain,
    ( v4_pre_topc(sK5(sK0,sK1,sK3),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f240,f169])).

fof(f240,plain,
    ( v4_pre_topc(sK5(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f168,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f321,plain,(
    ! [X3] :
      ( ~ v4_pre_topc(X3,sK1)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X3,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X3,u1_struct_0(sK2)),sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f319,f317])).

fof(f319,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X3,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X3,k2_struct_0(sK2)),sK2)
      | ~ v4_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(backward_demodulation,[],[f317,f229])).

fof(f229,plain,(
    ! [X3] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X3,k2_struct_0(sK2)),sK2)
      | ~ v4_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X3,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f224,f109])).

fof(f224,plain,(
    ! [X3] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X3,k2_struct_0(sK2)),sK2)
      | ~ v4_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X3,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f116,f167])).

fof(f167,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f93,f94])).

fof(f94,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
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
    inference(rectify,[],[f92])).

fof(f92,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
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
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',t43_pre_topc)).

fof(f116,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f87])).

fof(f12732,plain,(
    ! [X0] : k10_relat_1(sK3,X0) = k10_relat_1(sK3,k3_xboole_0(u1_struct_0(sK2),X0)) ),
    inference(forward_demodulation,[],[f12656,f324])).

fof(f324,plain,(
    ! [X2] : k10_relat_1(sK3,X2) = k10_relat_1(sK3,k3_xboole_0(k2_relat_1(sK3),X2)) ),
    inference(resolution,[],[f272,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',t168_relat_1)).

fof(f272,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f114,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',cc1_relset_1)).

fof(f12656,plain,(
    ! [X0] : k10_relat_1(sK3,k3_xboole_0(u1_struct_0(sK2),X0)) = k10_relat_1(sK3,k3_xboole_0(k2_relat_1(sK3),X0)) ),
    inference(superposition,[],[f324,f2990])).

fof(f2990,plain,(
    ! [X0] : k3_xboole_0(k2_relat_1(sK3),X0) = k3_xboole_0(k2_relat_1(sK3),k3_xboole_0(u1_struct_0(sK2),X0)) ),
    inference(superposition,[],[f151,f759])).

fof(f759,plain,(
    k3_xboole_0(k2_relat_1(sK3),u1_struct_0(sK2)) = k2_relat_1(sK3) ),
    inference(resolution,[],[f371,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',t28_xboole_1)).

fof(f371,plain,(
    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f370,f272])).

fof(f370,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK2))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f276,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',d19_relat_1)).

fof(f276,plain,(
    v5_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f114,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',cc2_relset_1)).

fof(f151,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t56_pre_topc.p',t16_xboole_1)).
%------------------------------------------------------------------------------
