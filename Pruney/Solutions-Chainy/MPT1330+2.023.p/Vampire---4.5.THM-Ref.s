%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:57 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  115 (1277 expanded)
%              Number of leaves         :   23 ( 447 expanded)
%              Depth                    :   24
%              Number of atoms          :  315 (7992 expanded)
%              Number of equality atoms :  128 (3153 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(subsumption_resolution,[],[f274,f55])).

fof(f55,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f274,plain,(
    k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f251,f260])).

fof(f260,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f259,f181])).

fof(f181,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k8_relset_1(X0,X1,k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f177,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f177,plain,(
    ! [X2,X0,X1] : k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f80,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f259,plain,(
    sK2 = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f258,f54])).

fof(f54,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f258,plain,(
    sK2 = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),sK2) ),
    inference(forward_demodulation,[],[f245,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f245,plain,(
    sK2 = k8_relset_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),sK2) ),
    inference(backward_demodulation,[],[f135,f235])).

fof(f235,plain,(
    k1_xboole_0 = k2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f234,f104])).

fof(f104,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f103,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f103,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(resolution,[],[f65,f100])).

fof(f100,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f97,f95])).

fof(f95,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f97,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f51,f94])).

fof(f94,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f234,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f233,f106])).

fof(f106,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f76,f100])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f233,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f232,f183])).

fof(f183,plain,(
    k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f182,f159])).

fof(f159,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(superposition,[],[f157,f126])).

fof(f126,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f123,f104])).

fof(f123,plain,
    ( sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f67,f118])).

fof(f118,plain,(
    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f117,f104])).

fof(f117,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f111,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f111,plain,(
    v5_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(resolution,[],[f77,f100])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f157,plain,(
    ! [X2] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2))) = k10_relat_1(sK2,X2) ),
    inference(forward_demodulation,[],[f154,f61])).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f154,plain,(
    ! [X2] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X2))) ),
    inference(resolution,[],[f140,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f140,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k1_relat_1(k5_relat_1(sK2,X6)) = k10_relat_1(sK2,k1_relat_1(X6)) ) ),
    inference(resolution,[],[f64,f104])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f182,plain,(
    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(superposition,[],[f99,f178])).

fof(f178,plain,(
    ! [X3] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X3) = k10_relat_1(sK2,X3) ),
    inference(resolution,[],[f80,f100])).

fof(f99,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f98,f95])).

fof(f98,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f53,f94])).

fof(f53,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f232,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f231,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f231,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f230,f100])).

fof(f230,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f229,f101])).

fof(f101,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f96,f95])).

fof(f96,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f50,f94])).

fof(f50,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X1,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | v1_partfun1(sK2,X1) ) ),
    inference(resolution,[],[f85,f49])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f135,plain,(
    sK2 = k8_relset_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2) ),
    inference(resolution,[],[f87,f100])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1 ) ),
    inference(forward_demodulation,[],[f70,f60])).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f251,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f183,f236])).

fof(f236,plain,(
    k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f52,f235])).

fof(f52,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:05:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.37  ipcrm: permission denied for id (804749313)
% 0.22/0.37  ipcrm: permission denied for id (806092802)
% 0.22/0.37  ipcrm: permission denied for id (804814851)
% 0.22/0.37  ipcrm: permission denied for id (806125572)
% 0.22/0.37  ipcrm: permission denied for id (806158341)
% 0.22/0.38  ipcrm: permission denied for id (804880390)
% 0.22/0.38  ipcrm: permission denied for id (804913159)
% 0.22/0.38  ipcrm: permission denied for id (806191112)
% 0.22/0.38  ipcrm: permission denied for id (809959433)
% 0.22/0.38  ipcrm: permission denied for id (806256650)
% 0.22/0.38  ipcrm: permission denied for id (806322188)
% 0.22/0.38  ipcrm: permission denied for id (804978701)
% 0.22/0.39  ipcrm: permission denied for id (810024974)
% 0.22/0.39  ipcrm: permission denied for id (805011471)
% 0.22/0.39  ipcrm: permission denied for id (810057744)
% 0.22/0.39  ipcrm: permission denied for id (810090513)
% 0.22/0.39  ipcrm: permission denied for id (806486034)
% 0.22/0.39  ipcrm: permission denied for id (806518803)
% 0.22/0.39  ipcrm: permission denied for id (806584341)
% 0.22/0.40  ipcrm: permission denied for id (806617110)
% 0.22/0.40  ipcrm: permission denied for id (806649879)
% 0.22/0.40  ipcrm: permission denied for id (806682648)
% 0.22/0.40  ipcrm: permission denied for id (810156057)
% 0.22/0.40  ipcrm: permission denied for id (806748186)
% 0.22/0.40  ipcrm: permission denied for id (806780955)
% 0.22/0.40  ipcrm: permission denied for id (806813724)
% 0.22/0.40  ipcrm: permission denied for id (806846493)
% 0.22/0.40  ipcrm: permission denied for id (811466782)
% 0.22/0.41  ipcrm: permission denied for id (810221599)
% 0.22/0.41  ipcrm: permission denied for id (806944800)
% 0.22/0.41  ipcrm: permission denied for id (805109793)
% 0.22/0.41  ipcrm: permission denied for id (806977570)
% 0.22/0.41  ipcrm: permission denied for id (807010339)
% 0.22/0.41  ipcrm: permission denied for id (807043108)
% 0.22/0.41  ipcrm: permission denied for id (807075877)
% 0.22/0.41  ipcrm: permission denied for id (807108646)
% 0.22/0.42  ipcrm: permission denied for id (807174183)
% 0.22/0.42  ipcrm: permission denied for id (807206952)
% 0.22/0.42  ipcrm: permission denied for id (810254377)
% 0.22/0.42  ipcrm: permission denied for id (810287146)
% 0.22/0.42  ipcrm: permission denied for id (807305259)
% 0.22/0.42  ipcrm: permission denied for id (807338028)
% 0.22/0.42  ipcrm: permission denied for id (805208109)
% 0.22/0.42  ipcrm: permission denied for id (807436334)
% 0.22/0.43  ipcrm: permission denied for id (807469103)
% 0.22/0.43  ipcrm: permission denied for id (807501872)
% 0.22/0.43  ipcrm: permission denied for id (810319921)
% 0.22/0.43  ipcrm: permission denied for id (811499570)
% 0.22/0.43  ipcrm: permission denied for id (807632947)
% 0.22/0.43  ipcrm: permission denied for id (807665716)
% 0.22/0.43  ipcrm: permission denied for id (812286005)
% 0.22/0.43  ipcrm: permission denied for id (805339190)
% 0.22/0.43  ipcrm: permission denied for id (807731255)
% 0.22/0.44  ipcrm: permission denied for id (807764024)
% 0.22/0.44  ipcrm: permission denied for id (807796793)
% 0.22/0.44  ipcrm: permission denied for id (807829562)
% 0.22/0.44  ipcrm: permission denied for id (807862331)
% 0.22/0.44  ipcrm: permission denied for id (805470268)
% 0.22/0.44  ipcrm: permission denied for id (805503037)
% 0.22/0.44  ipcrm: permission denied for id (807895102)
% 0.22/0.44  ipcrm: permission denied for id (805568575)
% 0.22/0.45  ipcrm: permission denied for id (807927872)
% 0.22/0.45  ipcrm: permission denied for id (805601345)
% 0.22/0.45  ipcrm: permission denied for id (807960642)
% 0.22/0.45  ipcrm: permission denied for id (807993411)
% 0.22/0.45  ipcrm: permission denied for id (808026180)
% 0.22/0.45  ipcrm: permission denied for id (810418245)
% 0.22/0.45  ipcrm: permission denied for id (808091718)
% 0.22/0.45  ipcrm: permission denied for id (808124487)
% 0.22/0.46  ipcrm: permission denied for id (810451016)
% 0.22/0.46  ipcrm: permission denied for id (810483785)
% 0.22/0.46  ipcrm: permission denied for id (808222794)
% 0.22/0.46  ipcrm: permission denied for id (812318795)
% 0.22/0.46  ipcrm: permission denied for id (808288332)
% 0.22/0.46  ipcrm: permission denied for id (808321101)
% 0.22/0.46  ipcrm: permission denied for id (808353870)
% 0.22/0.46  ipcrm: permission denied for id (811696207)
% 0.22/0.47  ipcrm: permission denied for id (812351568)
% 0.22/0.47  ipcrm: permission denied for id (810614865)
% 0.22/0.47  ipcrm: permission denied for id (810647634)
% 0.22/0.47  ipcrm: permission denied for id (808517715)
% 0.22/0.47  ipcrm: permission denied for id (805765204)
% 0.22/0.47  ipcrm: permission denied for id (811761749)
% 0.22/0.47  ipcrm: permission denied for id (810713174)
% 0.22/0.47  ipcrm: permission denied for id (808616023)
% 0.22/0.47  ipcrm: permission denied for id (805797976)
% 0.22/0.48  ipcrm: permission denied for id (810745945)
% 0.22/0.48  ipcrm: permission denied for id (808681562)
% 0.22/0.48  ipcrm: permission denied for id (808714331)
% 0.22/0.48  ipcrm: permission denied for id (810778716)
% 0.22/0.48  ipcrm: permission denied for id (810811485)
% 0.22/0.48  ipcrm: permission denied for id (808845406)
% 0.22/0.48  ipcrm: permission denied for id (810844255)
% 0.22/0.49  ipcrm: permission denied for id (808943713)
% 0.22/0.49  ipcrm: permission denied for id (811827298)
% 0.22/0.49  ipcrm: permission denied for id (809042019)
% 0.22/0.49  ipcrm: permission denied for id (809074788)
% 0.22/0.49  ipcrm: permission denied for id (809107557)
% 0.22/0.49  ipcrm: permission denied for id (810942566)
% 0.22/0.49  ipcrm: permission denied for id (812417127)
% 0.22/0.49  ipcrm: permission denied for id (811008104)
% 0.22/0.50  ipcrm: permission denied for id (809238633)
% 0.22/0.50  ipcrm: permission denied for id (809271402)
% 0.22/0.50  ipcrm: permission denied for id (811892843)
% 0.22/0.50  ipcrm: permission denied for id (809336940)
% 0.22/0.50  ipcrm: permission denied for id (811958381)
% 0.22/0.50  ipcrm: permission denied for id (809402478)
% 0.22/0.50  ipcrm: permission denied for id (811991151)
% 0.22/0.50  ipcrm: permission denied for id (809468016)
% 0.22/0.51  ipcrm: permission denied for id (812023921)
% 0.22/0.51  ipcrm: permission denied for id (805929074)
% 0.22/0.51  ipcrm: permission denied for id (812449907)
% 0.22/0.51  ipcrm: permission denied for id (812089460)
% 0.22/0.51  ipcrm: permission denied for id (809599093)
% 0.22/0.51  ipcrm: permission denied for id (809631862)
% 0.22/0.51  ipcrm: permission denied for id (811237495)
% 0.22/0.51  ipcrm: permission denied for id (812122232)
% 0.22/0.51  ipcrm: permission denied for id (809730169)
% 0.22/0.52  ipcrm: permission denied for id (811303034)
% 0.22/0.52  ipcrm: permission denied for id (812155003)
% 0.22/0.52  ipcrm: permission denied for id (805994620)
% 0.22/0.52  ipcrm: permission denied for id (809828477)
% 0.22/0.52  ipcrm: permission denied for id (806027390)
% 0.22/0.52  ipcrm: permission denied for id (809861247)
% 0.38/0.66  % (7808)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.38/0.66  % (7808)Refutation not found, incomplete strategy% (7808)------------------------------
% 0.38/0.66  % (7808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (7808)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (7808)Memory used [KB]: 10746
% 0.38/0.66  % (7808)Time elapsed: 0.093 s
% 0.38/0.66  % (7808)------------------------------
% 0.38/0.66  % (7808)------------------------------
% 0.38/0.67  % (7813)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.38/0.67  % (7807)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.38/0.68  % (7816)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.38/0.68  % (7812)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.38/0.68  % (7828)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.38/0.68  % (7828)Refutation not found, incomplete strategy% (7828)------------------------------
% 0.38/0.68  % (7828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.68  % (7828)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.68  
% 0.38/0.68  % (7828)Memory used [KB]: 10874
% 0.38/0.68  % (7828)Time elapsed: 0.116 s
% 0.38/0.68  % (7828)------------------------------
% 0.38/0.68  % (7828)------------------------------
% 0.38/0.69  % (7813)Refutation found. Thanks to Tanya!
% 0.38/0.69  % SZS status Theorem for theBenchmark
% 0.38/0.69  % SZS output start Proof for theBenchmark
% 0.38/0.69  fof(f294,plain,(
% 0.38/0.69    $false),
% 0.38/0.69    inference(subsumption_resolution,[],[f274,f55])).
% 0.38/0.69  fof(f55,plain,(
% 0.38/0.69    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.38/0.69    inference(cnf_transformation,[],[f10])).
% 0.38/0.69  fof(f10,axiom,(
% 0.38/0.69    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.38/0.69  fof(f274,plain,(
% 0.38/0.69    k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.38/0.69    inference(backward_demodulation,[],[f251,f260])).
% 0.38/0.69  fof(f260,plain,(
% 0.38/0.69    k1_xboole_0 = sK2),
% 0.38/0.69    inference(forward_demodulation,[],[f259,f181])).
% 0.38/0.69  fof(f181,plain,(
% 0.38/0.69    ( ! [X2,X0,X1] : (k1_xboole_0 = k8_relset_1(X0,X1,k1_xboole_0,X2)) )),
% 0.38/0.69    inference(forward_demodulation,[],[f177,f59])).
% 0.38/0.69  fof(f59,plain,(
% 0.38/0.69    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f8])).
% 0.38/0.69  fof(f8,axiom,(
% 0.38/0.69    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.38/0.69  fof(f177,plain,(
% 0.38/0.69    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2)) )),
% 0.38/0.69    inference(resolution,[],[f80,f58])).
% 0.38/0.69  fof(f58,plain,(
% 0.38/0.69    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.38/0.69    inference(cnf_transformation,[],[f2])).
% 0.38/0.69  fof(f2,axiom,(
% 0.38/0.69    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.38/0.69  fof(f80,plain,(
% 0.38/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f38])).
% 0.38/0.69  fof(f38,plain,(
% 0.38/0.69    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.69    inference(ennf_transformation,[],[f15])).
% 0.38/0.69  fof(f15,axiom,(
% 0.38/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.38/0.69  fof(f259,plain,(
% 0.38/0.69    sK2 = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)),
% 0.38/0.69    inference(forward_demodulation,[],[f258,f54])).
% 0.38/0.69  fof(f54,plain,(
% 0.38/0.69    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.38/0.69    inference(cnf_transformation,[],[f13])).
% 0.38/0.69  fof(f13,axiom,(
% 0.38/0.69    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.38/0.69  fof(f258,plain,(
% 0.38/0.69    sK2 = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),sK2)),
% 0.38/0.69    inference(forward_demodulation,[],[f245,f82])).
% 0.38/0.69  fof(f82,plain,(
% 0.38/0.69    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.38/0.69    inference(equality_resolution,[],[f75])).
% 0.38/0.69  fof(f75,plain,(
% 0.38/0.69    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.38/0.69    inference(cnf_transformation,[],[f46])).
% 0.38/0.69  fof(f46,plain,(
% 0.38/0.69    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.38/0.69    inference(flattening,[],[f45])).
% 0.38/0.69  fof(f45,plain,(
% 0.38/0.69    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.38/0.69    inference(nnf_transformation,[],[f1])).
% 0.38/0.69  fof(f1,axiom,(
% 0.38/0.69    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.38/0.69  fof(f245,plain,(
% 0.38/0.69    sK2 = k8_relset_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),sK2)),
% 0.38/0.69    inference(backward_demodulation,[],[f135,f235])).
% 0.38/0.69  fof(f235,plain,(
% 0.38/0.69    k1_xboole_0 = k2_struct_0(sK1)),
% 0.38/0.69    inference(subsumption_resolution,[],[f234,f104])).
% 0.38/0.69  fof(f104,plain,(
% 0.38/0.69    v1_relat_1(sK2)),
% 0.38/0.69    inference(subsumption_resolution,[],[f103,f66])).
% 0.38/0.69  fof(f66,plain,(
% 0.38/0.69    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.38/0.69    inference(cnf_transformation,[],[f7])).
% 0.38/0.69  fof(f7,axiom,(
% 0.38/0.69    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.38/0.69  fof(f103,plain,(
% 0.38/0.69    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 0.38/0.69    inference(resolution,[],[f65,f100])).
% 0.38/0.69  fof(f100,plain,(
% 0.38/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.38/0.69    inference(backward_demodulation,[],[f97,f95])).
% 0.38/0.69  fof(f95,plain,(
% 0.38/0.69    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.38/0.69    inference(resolution,[],[f63,f48])).
% 0.38/0.69  fof(f48,plain,(
% 0.38/0.69    l1_struct_0(sK1)),
% 0.38/0.69    inference(cnf_transformation,[],[f42])).
% 0.38/0.69  fof(f42,plain,(
% 0.38/0.69    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.38/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f41,f40,f39])).
% 0.38/0.69  fof(f39,plain,(
% 0.38/0.69    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.38/0.69    introduced(choice_axiom,[])).
% 0.38/0.69  fof(f40,plain,(
% 0.38/0.69    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.38/0.69    introduced(choice_axiom,[])).
% 0.38/0.69  fof(f41,plain,(
% 0.38/0.69    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.38/0.69    introduced(choice_axiom,[])).
% 0.38/0.69  fof(f25,plain,(
% 0.38/0.69    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.38/0.69    inference(flattening,[],[f24])).
% 0.38/0.69  fof(f24,plain,(
% 0.38/0.69    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.38/0.69    inference(ennf_transformation,[],[f22])).
% 0.38/0.69  fof(f22,negated_conjecture,(
% 0.38/0.69    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.38/0.69    inference(negated_conjecture,[],[f21])).
% 0.38/0.69  fof(f21,conjecture,(
% 0.38/0.69    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.38/0.69  fof(f63,plain,(
% 0.38/0.69    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f26])).
% 0.38/0.69  fof(f26,plain,(
% 0.38/0.69    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.38/0.69    inference(ennf_transformation,[],[f20])).
% 0.38/0.69  fof(f20,axiom,(
% 0.38/0.69    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.38/0.69  fof(f97,plain,(
% 0.38/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.38/0.69    inference(backward_demodulation,[],[f51,f94])).
% 0.38/0.69  fof(f94,plain,(
% 0.38/0.69    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.38/0.69    inference(resolution,[],[f63,f47])).
% 0.38/0.69  fof(f47,plain,(
% 0.38/0.69    l1_struct_0(sK0)),
% 0.38/0.69    inference(cnf_transformation,[],[f42])).
% 0.38/0.69  fof(f51,plain,(
% 0.38/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.38/0.69    inference(cnf_transformation,[],[f42])).
% 0.38/0.69  fof(f65,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f28])).
% 0.38/0.69  fof(f28,plain,(
% 0.38/0.69    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.38/0.69    inference(ennf_transformation,[],[f4])).
% 0.38/0.69  fof(f4,axiom,(
% 0.38/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.38/0.69  fof(f234,plain,(
% 0.38/0.69    k1_xboole_0 = k2_struct_0(sK1) | ~v1_relat_1(sK2)),
% 0.38/0.69    inference(subsumption_resolution,[],[f233,f106])).
% 0.38/0.69  fof(f106,plain,(
% 0.38/0.69    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.38/0.69    inference(resolution,[],[f76,f100])).
% 0.38/0.69  fof(f76,plain,(
% 0.38/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f35])).
% 0.38/0.69  fof(f35,plain,(
% 0.38/0.69    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.69    inference(ennf_transformation,[],[f14])).
% 0.38/0.69  fof(f14,axiom,(
% 0.38/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.38/0.69  fof(f233,plain,(
% 0.38/0.69    k1_xboole_0 = k2_struct_0(sK1) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 0.38/0.69    inference(subsumption_resolution,[],[f232,f183])).
% 0.38/0.69  fof(f183,plain,(
% 0.38/0.69    k2_struct_0(sK0) != k1_relat_1(sK2)),
% 0.38/0.69    inference(forward_demodulation,[],[f182,f159])).
% 0.38/0.69  fof(f159,plain,(
% 0.38/0.69    k1_relat_1(sK2) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.38/0.69    inference(superposition,[],[f157,f126])).
% 0.38/0.69  fof(f126,plain,(
% 0.38/0.69    sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1)))),
% 0.38/0.69    inference(subsumption_resolution,[],[f123,f104])).
% 0.38/0.69  fof(f123,plain,(
% 0.38/0.69    sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1))) | ~v1_relat_1(sK2)),
% 0.38/0.69    inference(resolution,[],[f67,f118])).
% 0.38/0.69  fof(f118,plain,(
% 0.38/0.69    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))),
% 0.38/0.69    inference(subsumption_resolution,[],[f117,f104])).
% 0.38/0.69  fof(f117,plain,(
% 0.38/0.69    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | ~v1_relat_1(sK2)),
% 0.38/0.69    inference(resolution,[],[f111,f68])).
% 0.38/0.69  fof(f68,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f43])).
% 0.38/0.69  fof(f43,plain,(
% 0.38/0.69    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.38/0.69    inference(nnf_transformation,[],[f31])).
% 0.38/0.69  fof(f31,plain,(
% 0.38/0.69    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.38/0.69    inference(ennf_transformation,[],[f5])).
% 0.38/0.69  fof(f5,axiom,(
% 0.38/0.69    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.38/0.69  fof(f111,plain,(
% 0.38/0.69    v5_relat_1(sK2,k2_struct_0(sK1))),
% 0.38/0.69    inference(resolution,[],[f77,f100])).
% 0.38/0.69  fof(f77,plain,(
% 0.38/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f35])).
% 0.38/0.69  fof(f67,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f30])).
% 0.38/0.69  fof(f30,plain,(
% 0.38/0.69    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.38/0.69    inference(flattening,[],[f29])).
% 0.38/0.69  fof(f29,plain,(
% 0.38/0.69    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.38/0.69    inference(ennf_transformation,[],[f12])).
% 0.38/0.69  fof(f12,axiom,(
% 0.38/0.69    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.38/0.69  fof(f157,plain,(
% 0.38/0.69    ( ! [X2] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2))) = k10_relat_1(sK2,X2)) )),
% 0.38/0.69    inference(forward_demodulation,[],[f154,f61])).
% 0.38/0.69  fof(f61,plain,(
% 0.38/0.69    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.38/0.69    inference(cnf_transformation,[],[f11])).
% 0.38/0.69  fof(f11,axiom,(
% 0.38/0.69    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.38/0.69  fof(f154,plain,(
% 0.38/0.69    ( ! [X2] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X2)))) )),
% 0.38/0.69    inference(resolution,[],[f140,f57])).
% 0.38/0.69  fof(f57,plain,(
% 0.38/0.69    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.38/0.69    inference(cnf_transformation,[],[f6])).
% 0.38/0.69  fof(f6,axiom,(
% 0.38/0.69    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.38/0.69  fof(f140,plain,(
% 0.38/0.69    ( ! [X6] : (~v1_relat_1(X6) | k1_relat_1(k5_relat_1(sK2,X6)) = k10_relat_1(sK2,k1_relat_1(X6))) )),
% 0.38/0.69    inference(resolution,[],[f64,f104])).
% 0.38/0.69  fof(f64,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.38/0.69    inference(cnf_transformation,[],[f27])).
% 0.38/0.69  fof(f27,plain,(
% 0.38/0.69    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.38/0.69    inference(ennf_transformation,[],[f9])).
% 0.38/0.69  fof(f9,axiom,(
% 0.38/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.38/0.69  fof(f182,plain,(
% 0.38/0.69    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.38/0.69    inference(superposition,[],[f99,f178])).
% 0.38/0.69  fof(f178,plain,(
% 0.38/0.69    ( ! [X3] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X3) = k10_relat_1(sK2,X3)) )),
% 0.38/0.69    inference(resolution,[],[f80,f100])).
% 0.38/0.69  fof(f99,plain,(
% 0.38/0.69    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.38/0.69    inference(backward_demodulation,[],[f98,f95])).
% 0.38/0.69  fof(f98,plain,(
% 0.38/0.69    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.38/0.69    inference(backward_demodulation,[],[f53,f94])).
% 0.38/0.69  fof(f53,plain,(
% 0.38/0.69    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.38/0.69    inference(cnf_transformation,[],[f42])).
% 0.38/0.69  fof(f232,plain,(
% 0.38/0.69    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 0.38/0.69    inference(resolution,[],[f231,f71])).
% 0.38/0.69  fof(f71,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f44])).
% 0.38/0.69  fof(f44,plain,(
% 0.38/0.69    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.38/0.69    inference(nnf_transformation,[],[f34])).
% 0.38/0.69  fof(f34,plain,(
% 0.38/0.69    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.38/0.69    inference(flattening,[],[f33])).
% 0.38/0.69  fof(f33,plain,(
% 0.38/0.69    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.38/0.69    inference(ennf_transformation,[],[f16])).
% 0.38/0.69  fof(f16,axiom,(
% 0.38/0.69    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.38/0.69  fof(f231,plain,(
% 0.38/0.69    v1_partfun1(sK2,k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.38/0.69    inference(subsumption_resolution,[],[f230,f100])).
% 0.38/0.69  fof(f230,plain,(
% 0.38/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.38/0.69    inference(resolution,[],[f229,f101])).
% 0.38/0.69  fof(f101,plain,(
% 0.38/0.69    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.38/0.69    inference(backward_demodulation,[],[f96,f95])).
% 0.38/0.69  fof(f96,plain,(
% 0.38/0.69    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.38/0.69    inference(backward_demodulation,[],[f50,f94])).
% 0.38/0.69  fof(f50,plain,(
% 0.38/0.69    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.38/0.69    inference(cnf_transformation,[],[f42])).
% 0.38/0.69  fof(f229,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | v1_partfun1(sK2,X1)) )),
% 0.38/0.69    inference(resolution,[],[f85,f49])).
% 0.38/0.69  fof(f49,plain,(
% 0.38/0.69    v1_funct_1(sK2)),
% 0.38/0.69    inference(cnf_transformation,[],[f42])).
% 0.38/0.69  fof(f85,plain,(
% 0.38/0.69    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.38/0.69    inference(duplicate_literal_removal,[],[f78])).
% 0.38/0.69  fof(f78,plain,(
% 0.38/0.69    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f37])).
% 0.38/0.69  fof(f37,plain,(
% 0.38/0.69    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.38/0.69    inference(flattening,[],[f36])).
% 0.38/0.69  fof(f36,plain,(
% 0.38/0.69    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.38/0.69    inference(ennf_transformation,[],[f18])).
% 0.38/0.69  fof(f18,axiom,(
% 0.38/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.38/0.69  fof(f135,plain,(
% 0.38/0.69    sK2 = k8_relset_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2)),
% 0.38/0.69    inference(resolution,[],[f87,f100])).
% 0.38/0.69  fof(f87,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1) )),
% 0.38/0.69    inference(forward_demodulation,[],[f70,f60])).
% 0.38/0.69  fof(f60,plain,(
% 0.38/0.69    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f17])).
% 0.38/0.69  fof(f17,axiom,(
% 0.38/0.69    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.38/0.69  fof(f70,plain,(
% 0.38/0.69    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.69    inference(cnf_transformation,[],[f32])).
% 0.38/0.69  fof(f32,plain,(
% 0.38/0.69    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.38/0.69    inference(ennf_transformation,[],[f19])).
% 0.38/0.69  fof(f19,axiom,(
% 0.38/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.38/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 0.38/0.69  fof(f251,plain,(
% 0.38/0.69    k1_xboole_0 != k1_relat_1(sK2)),
% 0.38/0.69    inference(backward_demodulation,[],[f183,f236])).
% 0.38/0.69  fof(f236,plain,(
% 0.38/0.69    k1_xboole_0 = k2_struct_0(sK0)),
% 0.38/0.69    inference(subsumption_resolution,[],[f52,f235])).
% 0.38/0.69  fof(f52,plain,(
% 0.38/0.69    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.38/0.69    inference(cnf_transformation,[],[f42])).
% 0.38/0.69  % SZS output end Proof for theBenchmark
% 0.38/0.69  % (7813)------------------------------
% 0.38/0.69  % (7813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.69  % (7813)Termination reason: Refutation
% 0.38/0.69  
% 0.38/0.69  % (7813)Memory used [KB]: 6396
% 0.38/0.69  % (7813)Time elapsed: 0.107 s
% 0.38/0.69  % (7813)------------------------------
% 0.38/0.69  % (7813)------------------------------
% 0.38/0.69  % (7671)Success in time 0.323 s
%------------------------------------------------------------------------------
