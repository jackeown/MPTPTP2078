%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 696 expanded)
%              Number of leaves         :   13 ( 128 expanded)
%              Depth                    :   22
%              Number of atoms          :  333 (2843 expanded)
%              Number of equality atoms :   35 ( 425 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f676,plain,(
    $false ),
    inference(subsumption_resolution,[],[f618,f118])).

fof(f118,plain,(
    ~ r2_hidden(sK7(sK4,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f100,f117])).

fof(f117,plain,(
    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f116,f63])).

fof(f63,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f116,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f110,f34])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f110,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f83,plain,(
    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f78,f63])).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f76,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f76,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f33,f73])).

fof(f73,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f58,f35])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f33,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f100,plain,
    ( ~ r2_hidden(sK7(sK4,sK2,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK7(sK4,sK2,sK3)) ),
    inference(resolution,[],[f85,f32])).

fof(f32,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f80,f63])).

fof(f80,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f76,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f618,plain,(
    r2_hidden(sK7(sK4,sK2,sK3),sK0) ),
    inference(backward_demodulation,[],[f84,f607])).

fof(f607,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f133,f606])).

fof(f606,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f605,f323])).

fof(f323,plain,
    ( v1_xboole_0(sK0)
    | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f322,f63])).

fof(f322,plain,
    ( v1_xboole_0(sK0)
    | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f315,f34])).

fof(f315,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f275,f54])).

fof(f275,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f274,f131])).

fof(f131,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(resolution,[],[f74,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f71,f73])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f57,f35])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
      | m1_subset_1(sK4,X0) ) ),
    inference(backward_demodulation,[],[f66,f73])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0))
      | m1_subset_1(sK4,X0) ) ),
    inference(resolution,[],[f56,f33])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f274,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    inference(subsumption_resolution,[],[f268,f102])).

fof(f102,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f268,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    inference(resolution,[],[f126,f76])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) ) ),
    inference(subsumption_resolution,[],[f125,f120])).

fof(f120,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f65,f113])).

fof(f113,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f83,f41])).

fof(f65,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f122,f35])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f37,f73])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f605,plain,
    ( sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f305,f307])).

fof(f307,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0)
    | v1_xboole_0(sK0) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK0)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(resolution,[],[f263,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f263,plain,
    ( m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f262,f131])).

fof(f262,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f256,f102])).

fof(f256,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(resolution,[],[f130,f76])).

fof(f130,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) ) ),
    inference(subsumption_resolution,[],[f129,f120])).

fof(f129,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f124,f35])).

fof(f124,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f36,f73])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f305,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f302,f41])).

fof(f302,plain,
    ( v1_xboole_0(sK0)
    | ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) ),
    inference(resolution,[],[f251,f32])).

fof(f251,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f250,f131])).

fof(f250,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f244,f102])).

fof(f244,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) ),
    inference(resolution,[],[f128,f76])).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2) ) ),
    inference(subsumption_resolution,[],[f127,f120])).

fof(f127,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f123,f35])).

fof(f123,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f38,f73])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK5(X1,X2,X3,X4),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f133,plain,
    ( ~ v1_xboole_0(sK0)
    | sK0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f88,f41])).

fof(f88,plain,
    ( r2_hidden(sK8(sK0,sK3),sK0)
    | sK0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f87,f69])).

fof(f69,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f87,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK8(sK0,sK3),sK0) ),
    inference(resolution,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK8(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f84,plain,(
    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f79,f63])).

fof(f79,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f76,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (20225)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (20219)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (20217)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (20211)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (20221)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (20206)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (20207)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (20223)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (20208)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (20206)Refutation not found, incomplete strategy% (20206)------------------------------
% 0.21/0.49  % (20206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20206)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20206)Memory used [KB]: 10618
% 0.21/0.49  % (20206)Time elapsed: 0.070 s
% 0.21/0.49  % (20206)------------------------------
% 0.21/0.49  % (20206)------------------------------
% 0.21/0.49  % (20205)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (20226)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (20217)Refutation not found, incomplete strategy% (20217)------------------------------
% 0.21/0.49  % (20217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20217)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20217)Memory used [KB]: 11001
% 0.21/0.49  % (20217)Time elapsed: 0.091 s
% 0.21/0.49  % (20217)------------------------------
% 0.21/0.49  % (20217)------------------------------
% 0.21/0.49  % (20210)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (20212)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (20215)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (20218)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (20214)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (20220)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (20213)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (20216)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (20224)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (20222)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (20226)Refutation not found, incomplete strategy% (20226)------------------------------
% 0.21/0.51  % (20226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20226)Memory used [KB]: 10618
% 0.21/0.51  % (20226)Time elapsed: 0.102 s
% 0.21/0.51  % (20226)------------------------------
% 0.21/0.51  % (20226)------------------------------
% 0.21/0.51  % (20223)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f676,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f618,f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ~r2_hidden(sK7(sK4,sK2,sK3),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f100,f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f116,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f48,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v1_funct_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f83,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f78,f63])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f76,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.54    inference(backward_demodulation,[],[f33,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.21/0.54    inference(resolution,[],[f58,f35])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ~r2_hidden(sK7(sK4,sK2,sK3),sK0) | sK4 != k1_funct_1(sK3,sK7(sK4,sK2,sK3))),
% 0.21/0.54    inference(resolution,[],[f85,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f80,f63])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f76,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f618,plain,(
% 0.21/0.54    r2_hidden(sK7(sK4,sK2,sK3),sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f84,f607])).
% 0.21/0.54  fof(f607,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f133,f606])).
% 0.21/0.54  fof(f606,plain,(
% 0.21/0.54    v1_xboole_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f605,f323])).
% 0.21/0.54  fof(f323,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f322,f63])).
% 0.21/0.54  fof(f322,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f315,f34])).
% 0.21/0.54  fof(f315,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f275,f54])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | v1_xboole_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f274,f131])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    m1_subset_1(sK4,sK1)),
% 0.21/0.54    inference(resolution,[],[f74,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f71,f73])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))) )),
% 0.21/0.54    inference(resolution,[],[f57,f35])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f66,f73])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) )),
% 0.21/0.54    inference(resolution,[],[f56,f33])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f268,f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ~v1_xboole_0(sK2)),
% 0.21/0.54    inference(resolution,[],[f85,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.21/0.54    inference(resolution,[],[f126,f76])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f125,f120])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f65,f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ~v1_xboole_0(sK3)),
% 0.21/0.54    inference(resolution,[],[f83,f41])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1) | v1_xboole_0(sK3)),
% 0.21/0.54    inference(resolution,[],[f42,f35])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | v1_xboole_0(sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f122,f35])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | v1_xboole_0(sK1)) )),
% 0.21/0.54    inference(superposition,[],[f37,f73])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.54  fof(f605,plain,(
% 0.21/0.54    sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | v1_xboole_0(sK0)),
% 0.21/0.54    inference(resolution,[],[f305,f307])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0) | v1_xboole_0(sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f306])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | v1_xboole_0(sK0) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.21/0.54    inference(resolution,[],[f263,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.54  fof(f263,plain,(
% 0.21/0.54    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | v1_xboole_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f262,f131])).
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f256,f102])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.21/0.54    inference(resolution,[],[f130,f76])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f129,f120])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) | v1_xboole_0(sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f124,f35])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) | v1_xboole_0(sK1)) )),
% 0.21/0.54    inference(superposition,[],[f36,f73])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK5(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0) | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f302,f41])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0) | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))),
% 0.21/0.54    inference(resolution,[],[f251,f32])).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | v1_xboole_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f250,f131])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f244,f102])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)),
% 0.21/0.54    inference(resolution,[],[f128,f76])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f127,f120])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2) | v1_xboole_0(sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f123,f35])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2) | v1_xboole_0(sK1)) )),
% 0.21/0.54    inference(superposition,[],[f38,f73])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK5(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0) | sK0 = k1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f88,f41])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    r2_hidden(sK8(sK0,sK3),sK0) | sK0 = k1_relat_1(sK3)),
% 0.21/0.54    inference(forward_demodulation,[],[f87,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.54    inference(resolution,[],[f49,f35])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK8(sK0,sK3),sK0)),
% 0.21/0.54    inference(resolution,[],[f50,f35])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK8(X1,X2),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f79,f63])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f76,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (20223)------------------------------
% 0.21/0.54  % (20223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20223)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (20223)Memory used [KB]: 2174
% 0.21/0.54  % (20223)Time elapsed: 0.084 s
% 0.21/0.54  % (20223)------------------------------
% 0.21/0.54  % (20223)------------------------------
% 0.21/0.54  % (20202)Success in time 0.184 s
%------------------------------------------------------------------------------
