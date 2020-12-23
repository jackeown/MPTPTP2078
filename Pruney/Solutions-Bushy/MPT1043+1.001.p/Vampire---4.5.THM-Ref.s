%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1043+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   76 (8185 expanded)
%              Number of leaves         :   10 (2208 expanded)
%              Depth                    :   19
%              Number of atoms          :  190 (26085 expanded)
%              Number of equality atoms :   15 ( 699 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(subsumption_resolution,[],[f193,f167])).

fof(f167,plain,(
    m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(backward_demodulation,[],[f96,f143])).

fof(f143,plain,(
    o_0_0_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f103,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f32,f105])).

fof(f105,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f93,f95,f78,f96,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(f78,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),k1_funct_2(sK0,o_0_0_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f66,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f66,plain,(
    ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f31,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r1_tarski(k5_partfun1(sK0,X0,sK2),k1_funct_2(sK0,X0)) ) ),
    inference(superposition,[],[f52,f32])).

fof(f52,plain,(
    ~ r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f30,f50])).

fof(f50,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f46,f47,f45,f48,f38])).

fof(f48,plain,(
    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f44,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f44,plain,(
    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f34])).

fof(f47,plain,(
    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f29,f44,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f44,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f95,plain,(
    v1_funct_2(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),sK0,o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f28,f65,f77,f41])).

fof(f77,plain,(
    r2_hidden(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),k5_partfun1(sK0,o_0_0_xboole_0,sK2)) ),
    inference(unit_resulting_resolution,[],[f66,f33])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f31,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(superposition,[],[f51,f32])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f29,f50])).

fof(f93,plain,(
    v1_funct_1(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f31,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(sK3(k5_partfun1(sK0,X0,sK2),k1_funct_2(sK0,X0))) ) ),
    inference(superposition,[],[f55,f32])).

fof(f55,plain,(
    v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f46,f50])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f103,plain,(
    v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f31,f28,f65,f92,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).

fof(f92,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,o_0_0_xboole_0,sK2)) ),
    inference(unit_resulting_resolution,[],[f31,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(k5_partfun1(sK0,X0,sK2)) ) ),
    inference(superposition,[],[f58,f32])).

fof(f58,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f49,f50])).

fof(f49,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f96,plain,(
    m1_subset_1(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f28,f65,f77,f42])).

fof(f193,plain,(
    ~ m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f165,f157,f166,f127])).

fof(f127,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | r2_hidden(X2,k1_funct_2(o_0_0_xboole_0,X1))
      | ~ v1_funct_2(X2,o_0_0_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f126,f105])).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | r2_hidden(X2,k1_funct_2(o_0_0_xboole_0,X1))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f116,f105])).

fof(f116,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(o_0_0_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(backward_demodulation,[],[f43,f105])).

fof(f43,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f166,plain,(
    v1_funct_2(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f95,f143])).

fof(f157,plain,(
    ~ r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(backward_demodulation,[],[f78,f143])).

fof(f165,plain,(
    v1_funct_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(backward_demodulation,[],[f93,f143])).

%------------------------------------------------------------------------------
