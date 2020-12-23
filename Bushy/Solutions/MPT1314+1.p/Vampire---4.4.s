%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t33_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:39 EDT 2019

% Result     : Theorem 0.95s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 182 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   20
%              Number of atoms          :  277 (1136 expanded)
%              Number of equality atoms :   42 ( 190 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5968,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5967,f125])).

fof(f125,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f124,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',dt_l1_pre_topc)).

fof(f124,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f121,f78])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v3_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f64,f63,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & sK1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(sK1,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v3_pre_topc(X3,sK2)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & v3_pre_topc(X1,X0)
        & m1_pre_topc(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v3_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(sK3,X2)
        & sK3 = X1
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',t33_tops_2)).

fof(f121,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f90,f80])).

fof(f80,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',dt_m1_pre_topc)).

fof(f5967,plain,(
    ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f5966,f131])).

fof(f131,plain,(
    r1_tarski(sK1,u1_struct_0(sK2)) ),
    inference(resolution,[],[f103,f116])).

fof(f116,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f82,f83])).

fof(f83,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f65])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',t3_subset)).

fof(f5966,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(superposition,[],[f5964,f87])).

fof(f87,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',d3_struct_0)).

fof(f5964,plain,(
    ~ r1_tarski(sK1,k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f5963,f115])).

fof(f115,plain,(
    ~ v3_pre_topc(sK1,sK2) ),
    inference(backward_demodulation,[],[f83,f84])).

fof(f84,plain,(
    ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f5963,plain,
    ( v3_pre_topc(sK1,sK2)
    | ~ r1_tarski(sK1,k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f5948,f80])).

fof(f5948,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v3_pre_topc(sK1,sK2)
    | ~ r1_tarski(sK1,k2_struct_0(sK2)) ),
    inference(resolution,[],[f4214,f116])).

fof(f4214,plain,(
    ! [X34] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X34)))
      | ~ m1_pre_topc(X34,sK0)
      | v3_pre_topc(sK1,X34)
      | ~ r1_tarski(sK1,k2_struct_0(X34)) ) ),
    inference(subsumption_resolution,[],[f4213,f78])).

fof(f4213,plain,(
    ! [X34] :
      ( v3_pre_topc(sK1,X34)
      | ~ m1_pre_topc(X34,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X34)))
      | ~ r1_tarski(sK1,k2_struct_0(X34)) ) ),
    inference(subsumption_resolution,[],[f4179,f81])).

fof(f81,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f4179,plain,(
    ! [X34] :
      ( v3_pre_topc(sK1,X34)
      | ~ v3_pre_topc(sK1,sK0)
      | ~ m1_pre_topc(X34,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X34)))
      | ~ r1_tarski(sK1,k2_struct_0(X34)) ) ),
    inference(resolution,[],[f926,f79])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f926,plain,(
    ! [X12,X13,X11] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X13)))
      | v3_pre_topc(X12,X11)
      | ~ v3_pre_topc(X12,X13)
      | ~ m1_pre_topc(X11,X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | ~ r1_tarski(X12,k2_struct_0(X11)) ) ),
    inference(superposition,[],[f417,f137])).

fof(f137,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X5,X4) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f99,f98])).

fof(f98,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',commutativity_k3_xboole_0)).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',t28_xboole_1)).

fof(f417,plain,(
    ! [X8,X7,X9] :
      ( v3_pre_topc(k3_xboole_0(k2_struct_0(X7),X8),X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ v3_pre_topc(X8,X9)
      | ~ m1_pre_topc(X7,X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(duplicate_literal_removal,[],[f412])).

fof(f412,plain,(
    ! [X8,X7,X9] :
      ( v3_pre_topc(k3_xboole_0(k2_struct_0(X7),X8),X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ v3_pre_topc(X8,X9)
      | ~ m1_pre_topc(X7,X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(superposition,[],[f222,f196])).

fof(f196,plain,(
    ! [X10,X8,X9] :
      ( k3_xboole_0(X9,X10) = k9_subset_1(X8,X10,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8)) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X10,X8,X9] :
      ( k3_xboole_0(X9,X10) = k9_subset_1(X8,X10,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8)) ) ),
    inference(superposition,[],[f109,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',redefinition_k9_subset_1)).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',commutativity_k9_subset_1)).

fof(f222,plain,(
    ! [X8,X7,X9] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X7),X8,k2_struct_0(X7)),X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ v3_pre_topc(X8,X9)
      | ~ m1_pre_topc(X7,X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(subsumption_resolution,[],[f218,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',dt_k9_subset_1)).

fof(f218,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X7),k2_struct_0(X7),X8),k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v3_pre_topc(X8,X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(X7),X8,k2_struct_0(X7)),X7)
      | ~ m1_pre_topc(X7,X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(superposition,[],[f114,f109])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t33_tops_2.p',t32_tops_2)).
%------------------------------------------------------------------------------
