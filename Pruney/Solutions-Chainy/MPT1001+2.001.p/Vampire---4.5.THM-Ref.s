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
% DateTime   : Thu Dec  3 13:03:35 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 430 expanded)
%              Number of leaves         :   10 (  85 expanded)
%              Depth                    :   23
%              Number of atoms          :  162 (1315 expanded)
%              Number of equality atoms :   63 ( 460 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(subsumption_resolution,[],[f126,f112])).

fof(f112,plain,(
    r2_hidden(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( sK1 != sK1
    | r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f66,f96])).

fof(f96,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f94,f61])).

fof(f61,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f58,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f58,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f29,f50])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f38,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f57,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f40,f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f94,plain,
    ( sK1 = k2_relat_1(sK2)
    | r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f93,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f93,plain,
    ( ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | sK1 = k2_relat_1(sK2)
    | sK1 = k2_relat_1(sK2) ),
    inference(superposition,[],[f90,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK4(sK1,k2_relat_1(sK2)),sK4(sK1,k2_relat_1(sK2))))
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f70,f61])).

fof(f70,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_relat_1(sK2))
      | k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK4(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2)))) ) ),
    inference(resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK2))
      | k1_xboole_0 = k10_relat_1(sK2,k2_tarski(X0,X0)) ) ),
    inference(resolution,[],[f45,f50])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k10_relat_1(X1,k2_tarski(X0,X0))
      | r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
      | r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f90,plain,(
    ! [X3] :
      ( k1_xboole_0 != k10_relat_1(sK2,k2_tarski(X3,X3))
      | ~ r2_hidden(X3,sK1)
      | sK1 = k2_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f68,f89])).

fof(f89,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f41,f26])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f68,plain,(
    ! [X3] :
      ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X3,X3))
      | ~ r2_hidden(X3,sK1)
      | sK1 = k2_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f42,f65])).

fof(f65,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f39,f26])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f42,plain,(
    ! [X3] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(X3,sK1)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X3,X3)) ) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f25,plain,(
    ! [X3] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(X3,sK1)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,
    ( r2_hidden(sK3,sK1)
    | sK1 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f23,f65])).

fof(f23,plain,
    ( r2_hidden(sK3,sK1)
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f126,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(forward_demodulation,[],[f125,f96])).

fof(f125,plain,(
    ~ r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f124,f50])).

fof(f124,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f123])).

% (16596)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(superposition,[],[f44,f121])).

fof(f121,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK3,sK3)) ),
    inference(superposition,[],[f111,f89])).

fof(f111,plain,(
    k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3)) ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,
    ( sK1 != sK1
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3)) ),
    inference(backward_demodulation,[],[f67,f96])).

fof(f67,plain,
    ( sK1 != k2_relat_1(sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3)) ),
    inference(backward_demodulation,[],[f43,f65])).

fof(f43,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3)) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k2_tarski(X0,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(definition_unfolding,[],[f31,f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:26:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (806060032)
% 0.15/0.37  ipcrm: permission denied for id (806092802)
% 0.15/0.37  ipcrm: permission denied for id (806223878)
% 0.15/0.38  ipcrm: permission denied for id (806256647)
% 0.15/0.38  ipcrm: permission denied for id (806289416)
% 0.15/0.38  ipcrm: permission denied for id (806322185)
% 0.15/0.38  ipcrm: permission denied for id (806387723)
% 0.15/0.38  ipcrm: permission denied for id (806420492)
% 0.15/0.39  ipcrm: permission denied for id (806486031)
% 0.15/0.39  ipcrm: permission denied for id (806551569)
% 0.15/0.40  ipcrm: permission denied for id (806715416)
% 0.15/0.40  ipcrm: permission denied for id (806748187)
% 0.15/0.41  ipcrm: permission denied for id (806813728)
% 0.22/0.41  ipcrm: permission denied for id (806846498)
% 0.22/0.41  ipcrm: permission denied for id (806912036)
% 0.22/0.42  ipcrm: permission denied for id (806977575)
% 0.22/0.43  ipcrm: permission denied for id (807075887)
% 0.22/0.43  ipcrm: permission denied for id (807174198)
% 0.22/0.44  ipcrm: permission denied for id (807239739)
% 0.22/0.45  ipcrm: permission denied for id (807305278)
% 0.22/0.45  ipcrm: permission denied for id (807338048)
% 0.22/0.45  ipcrm: permission denied for id (807403588)
% 0.22/0.46  ipcrm: permission denied for id (807436357)
% 0.22/0.46  ipcrm: permission denied for id (807469126)
% 0.22/0.46  ipcrm: permission denied for id (807600202)
% 0.22/0.47  ipcrm: permission denied for id (807632971)
% 0.22/0.49  ipcrm: permission denied for id (807862365)
% 0.22/0.49  ipcrm: permission denied for id (807927902)
% 0.22/0.51  ipcrm: permission denied for id (808190059)
% 0.22/0.51  ipcrm: permission denied for id (808222828)
% 0.22/0.52  ipcrm: permission denied for id (808321134)
% 0.22/0.52  ipcrm: permission denied for id (808353903)
% 0.22/0.52  ipcrm: permission denied for id (808386672)
% 0.22/0.52  ipcrm: permission denied for id (808419441)
% 0.22/0.52  ipcrm: permission denied for id (808452210)
% 0.22/0.52  ipcrm: permission denied for id (808484979)
% 0.22/0.53  ipcrm: permission denied for id (808517748)
% 0.22/0.53  ipcrm: permission denied for id (808550517)
% 0.22/0.54  ipcrm: permission denied for id (808583291)
% 0.22/0.54  ipcrm: permission denied for id (808648829)
% 0.22/0.54  ipcrm: permission denied for id (808681598)
% 0.22/0.54  ipcrm: permission denied for id (808714367)
% 1.50/0.72  % (16587)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.72  % (16588)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.72  % (16595)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.72  % (16604)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.73  % (16587)Refutation found. Thanks to Tanya!
% 1.50/0.73  % SZS status Theorem for theBenchmark
% 1.50/0.73  % (16603)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.73  % SZS output start Proof for theBenchmark
% 1.50/0.73  fof(f127,plain,(
% 1.50/0.73    $false),
% 1.50/0.73    inference(subsumption_resolution,[],[f126,f112])).
% 1.50/0.73  fof(f112,plain,(
% 1.50/0.73    r2_hidden(sK3,sK1)),
% 1.50/0.73    inference(trivial_inequality_removal,[],[f105])).
% 1.50/0.73  fof(f105,plain,(
% 1.50/0.73    sK1 != sK1 | r2_hidden(sK3,sK1)),
% 1.50/0.73    inference(backward_demodulation,[],[f66,f96])).
% 1.50/0.73  fof(f96,plain,(
% 1.50/0.73    sK1 = k2_relat_1(sK2)),
% 1.50/0.73    inference(subsumption_resolution,[],[f94,f61])).
% 1.50/0.73  fof(f61,plain,(
% 1.50/0.73    ~r1_tarski(sK1,k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2)),
% 1.50/0.73    inference(resolution,[],[f58,f34])).
% 1.50/0.73  fof(f34,plain,(
% 1.50/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.50/0.73    inference(cnf_transformation,[],[f2])).
% 1.50/0.73  fof(f2,axiom,(
% 1.50/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.73  fof(f58,plain,(
% 1.50/0.73    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.50/0.73    inference(resolution,[],[f57,f53])).
% 1.50/0.73  fof(f53,plain,(
% 1.50/0.73    ( ! [X0] : (~v5_relat_1(sK2,X0) | r1_tarski(k2_relat_1(sK2),X0)) )),
% 1.50/0.73    inference(resolution,[],[f29,f50])).
% 1.50/0.73  fof(f50,plain,(
% 1.50/0.73    v1_relat_1(sK2)),
% 1.50/0.73    inference(resolution,[],[f38,f26])).
% 1.50/0.73  fof(f26,plain,(
% 1.50/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.73    inference(cnf_transformation,[],[f15])).
% 1.50/0.73  fof(f15,plain,(
% 1.50/0.73    ? [X0,X1,X2] : ((! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.73    inference(ennf_transformation,[],[f13])).
% 1.50/0.73  fof(f13,plain,(
% 1.50/0.73    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.50/0.73    inference(pure_predicate_removal,[],[f12])).
% 1.50/0.73  fof(f12,plain,(
% 1.50/0.73    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.50/0.73    inference(pure_predicate_removal,[],[f11])).
% 1.50/0.73  fof(f11,negated_conjecture,(
% 1.50/0.73    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.50/0.73    inference(negated_conjecture,[],[f10])).
% 1.50/0.73  fof(f10,conjecture,(
% 1.50/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).
% 1.50/0.73  fof(f38,plain,(
% 1.50/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.50/0.73    inference(cnf_transformation,[],[f19])).
% 1.50/0.73  fof(f19,plain,(
% 1.50/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.73    inference(ennf_transformation,[],[f6])).
% 1.50/0.73  fof(f6,axiom,(
% 1.50/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.50/0.73  fof(f29,plain,(
% 1.50/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 1.50/0.73    inference(cnf_transformation,[],[f16])).
% 1.50/0.73  fof(f16,plain,(
% 1.50/0.73    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.73    inference(ennf_transformation,[],[f4])).
% 1.50/0.73  fof(f4,axiom,(
% 1.50/0.73    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.50/0.73  fof(f57,plain,(
% 1.50/0.73    v5_relat_1(sK2,sK1)),
% 1.50/0.73    inference(resolution,[],[f40,f26])).
% 1.50/0.73  fof(f40,plain,(
% 1.50/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.50/0.73    inference(cnf_transformation,[],[f21])).
% 1.50/0.73  fof(f21,plain,(
% 1.50/0.73    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.73    inference(ennf_transformation,[],[f14])).
% 1.50/0.73  fof(f14,plain,(
% 1.50/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.50/0.73    inference(pure_predicate_removal,[],[f7])).
% 1.50/0.73  fof(f7,axiom,(
% 1.50/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.50/0.73  fof(f94,plain,(
% 1.50/0.73    sK1 = k2_relat_1(sK2) | r1_tarski(sK1,k2_relat_1(sK2))),
% 1.50/0.73    inference(resolution,[],[f93,f36])).
% 1.50/0.73  fof(f36,plain,(
% 1.50/0.73    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.50/0.73    inference(cnf_transformation,[],[f18])).
% 1.50/0.73  fof(f18,plain,(
% 1.50/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.73    inference(ennf_transformation,[],[f1])).
% 1.50/0.73  fof(f1,axiom,(
% 1.50/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.73  fof(f93,plain,(
% 1.50/0.73    ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | sK1 = k2_relat_1(sK2)),
% 1.50/0.73    inference(trivial_inequality_removal,[],[f92])).
% 1.50/0.73  fof(f92,plain,(
% 1.50/0.73    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | sK1 = k2_relat_1(sK2)),
% 1.50/0.73    inference(duplicate_literal_removal,[],[f91])).
% 1.50/0.73  fof(f91,plain,(
% 1.50/0.73    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | sK1 = k2_relat_1(sK2) | sK1 = k2_relat_1(sK2)),
% 1.50/0.73    inference(superposition,[],[f90,f79])).
% 1.50/0.73  fof(f79,plain,(
% 1.50/0.73    k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK4(sK1,k2_relat_1(sK2)),sK4(sK1,k2_relat_1(sK2)))) | sK1 = k2_relat_1(sK2)),
% 1.50/0.73    inference(resolution,[],[f70,f61])).
% 1.50/0.73  fof(f70,plain,(
% 1.50/0.73    ( ! [X0] : (r1_tarski(X0,k2_relat_1(sK2)) | k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK4(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))))) )),
% 1.50/0.73    inference(resolution,[],[f69,f37])).
% 1.50/0.73  fof(f37,plain,(
% 1.50/0.73    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.50/0.73    inference(cnf_transformation,[],[f18])).
% 1.50/0.73  fof(f69,plain,(
% 1.50/0.73    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | k1_xboole_0 = k10_relat_1(sK2,k2_tarski(X0,X0))) )),
% 1.50/0.73    inference(resolution,[],[f45,f50])).
% 1.50/0.73  fof(f45,plain,(
% 1.50/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,k2_tarski(X0,X0)) | r2_hidden(X0,k2_relat_1(X1))) )),
% 1.50/0.73    inference(definition_unfolding,[],[f30,f27])).
% 1.50/0.73  fof(f27,plain,(
% 1.50/0.73    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.73    inference(cnf_transformation,[],[f3])).
% 1.50/0.73  fof(f3,axiom,(
% 1.50/0.73    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.73  fof(f30,plain,(
% 1.50/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | r2_hidden(X0,k2_relat_1(X1))) )),
% 1.50/0.73    inference(cnf_transformation,[],[f17])).
% 1.50/0.73  fof(f17,plain,(
% 1.50/0.73    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) | ~v1_relat_1(X1))),
% 1.50/0.73    inference(ennf_transformation,[],[f5])).
% 1.50/0.73  fof(f5,axiom,(
% 1.50/0.73    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 1.50/0.73  fof(f90,plain,(
% 1.50/0.73    ( ! [X3] : (k1_xboole_0 != k10_relat_1(sK2,k2_tarski(X3,X3)) | ~r2_hidden(X3,sK1) | sK1 = k2_relat_1(sK2)) )),
% 1.50/0.73    inference(backward_demodulation,[],[f68,f89])).
% 1.50/0.73  fof(f89,plain,(
% 1.50/0.73    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 1.50/0.73    inference(resolution,[],[f41,f26])).
% 1.50/0.73  fof(f41,plain,(
% 1.50/0.73    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.50/0.73    inference(cnf_transformation,[],[f22])).
% 1.50/0.73  fof(f22,plain,(
% 1.50/0.73    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.73    inference(ennf_transformation,[],[f9])).
% 1.50/0.73  fof(f9,axiom,(
% 1.50/0.73    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.50/0.73  fof(f68,plain,(
% 1.50/0.73    ( ! [X3] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X3,X3)) | ~r2_hidden(X3,sK1) | sK1 = k2_relat_1(sK2)) )),
% 1.50/0.73    inference(backward_demodulation,[],[f42,f65])).
% 1.50/0.73  fof(f65,plain,(
% 1.50/0.73    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.50/0.73    inference(resolution,[],[f39,f26])).
% 1.50/0.73  fof(f39,plain,(
% 1.50/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.50/0.73    inference(cnf_transformation,[],[f20])).
% 1.50/0.73  fof(f20,plain,(
% 1.50/0.73    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.73    inference(ennf_transformation,[],[f8])).
% 1.50/0.73  fof(f8,axiom,(
% 1.50/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.50/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.50/0.73  fof(f42,plain,(
% 1.50/0.73    ( ! [X3] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X3,X3))) )),
% 1.50/0.73    inference(definition_unfolding,[],[f25,f27])).
% 1.50/0.73  fof(f25,plain,(
% 1.50/0.73    ( ! [X3] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X3))) )),
% 1.50/0.73    inference(cnf_transformation,[],[f15])).
% 1.50/0.73  fof(f66,plain,(
% 1.50/0.73    r2_hidden(sK3,sK1) | sK1 != k2_relat_1(sK2)),
% 1.50/0.73    inference(backward_demodulation,[],[f23,f65])).
% 1.50/0.73  fof(f23,plain,(
% 1.50/0.73    r2_hidden(sK3,sK1) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.50/0.73    inference(cnf_transformation,[],[f15])).
% 1.50/0.73  fof(f126,plain,(
% 1.50/0.73    ~r2_hidden(sK3,sK1)),
% 1.50/0.73    inference(forward_demodulation,[],[f125,f96])).
% 1.50/0.73  fof(f125,plain,(
% 1.50/0.73    ~r2_hidden(sK3,k2_relat_1(sK2))),
% 1.50/0.73    inference(subsumption_resolution,[],[f124,f50])).
% 1.50/0.73  fof(f124,plain,(
% 1.50/0.73    ~v1_relat_1(sK2) | ~r2_hidden(sK3,k2_relat_1(sK2))),
% 1.50/0.73    inference(trivial_inequality_removal,[],[f123])).
% 1.50/0.73  % (16596)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.74  fof(f123,plain,(
% 1.50/0.74    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | ~r2_hidden(sK3,k2_relat_1(sK2))),
% 1.50/0.74    inference(superposition,[],[f44,f121])).
% 1.50/0.74  fof(f121,plain,(
% 1.50/0.74    k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK3,sK3))),
% 1.50/0.74    inference(superposition,[],[f111,f89])).
% 1.50/0.74  fof(f111,plain,(
% 1.50/0.74    k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3))),
% 1.50/0.74    inference(trivial_inequality_removal,[],[f106])).
% 1.50/0.74  fof(f106,plain,(
% 1.50/0.74    sK1 != sK1 | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3))),
% 1.50/0.74    inference(backward_demodulation,[],[f67,f96])).
% 1.50/0.74  fof(f67,plain,(
% 1.50/0.74    sK1 != k2_relat_1(sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3))),
% 1.50/0.74    inference(backward_demodulation,[],[f43,f65])).
% 1.50/0.74  fof(f43,plain,(
% 1.50/0.74    sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3))),
% 1.50/0.74    inference(definition_unfolding,[],[f24,f27])).
% 1.50/0.74  fof(f24,plain,(
% 1.50/0.74    sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 1.50/0.74    inference(cnf_transformation,[],[f15])).
% 1.50/0.74  fof(f44,plain,(
% 1.50/0.74    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k2_tarski(X0,X0)) | ~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 1.50/0.74    inference(definition_unfolding,[],[f31,f27])).
% 1.50/0.74  fof(f31,plain,(
% 1.50/0.74    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 1.50/0.74    inference(cnf_transformation,[],[f17])).
% 1.50/0.74  % SZS output end Proof for theBenchmark
% 1.50/0.74  % (16587)------------------------------
% 1.50/0.74  % (16587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.74  % (16587)Termination reason: Refutation
% 1.50/0.74  
% 1.50/0.74  % (16587)Memory used [KB]: 6268
% 1.50/0.74  % (16587)Time elapsed: 0.111 s
% 1.50/0.74  % (16587)------------------------------
% 1.50/0.74  % (16587)------------------------------
% 1.50/0.74  % (16411)Success in time 0.367 s
%------------------------------------------------------------------------------
