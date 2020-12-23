%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:52 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  214 (160494 expanded)
%              Number of leaves         :   21 (38188 expanded)
%              Depth                    :   50
%              Number of atoms          :  786 (861664 expanded)
%              Number of equality atoms :  163 (50398 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1244,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1243,f1216])).

fof(f1216,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK1) ),
    inference(resolution,[],[f1215,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1215,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | r2_relset_1(k1_xboole_0,k1_xboole_0,X2,sK1) ) ),
    inference(resolution,[],[f1126,f1014])).

fof(f1014,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f738,f980])).

fof(f980,plain,(
    sK1 = k2_funct_1(sK1) ),
    inference(resolution,[],[f978,f738])).

fof(f978,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_funct_1(sK1)))
      | sK1 = X5 ) ),
    inference(resolution,[],[f773,f751])).

fof(f751,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_funct_1(sK1))) ),
    inference(backward_demodulation,[],[f659,f723])).

fof(f723,plain,(
    k2_funct_1(sK1) = k6_partfun1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f722,f608])).

fof(f608,plain,(
    k2_funct_1(sK1) = k2_funct_2(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f117,f602])).

fof(f602,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f601,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f601,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f598,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f598,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f597])).

fof(f597,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f596,f575])).

fof(f575,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f574,f57])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f45])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f574,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f541,f56])).

fof(f56,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f541,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(sK1,X0,X1)
      | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f540,f57])).

fof(f540,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
      | ~ v3_funct_2(sK1,X0,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f295,f55])).

fof(f55,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK1,X0,sK0)
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
      | ~ v3_funct_2(sK1,X1,X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f294,f54])).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f294,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK1,X0,sK0)
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
      | ~ v1_funct_1(sK1)
      | ~ v3_funct_2(sK1,X1,X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f254,f279])).

fof(f279,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f273,f57])).

fof(f273,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK0 = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f264,f57])).

fof(f264,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK0 = k2_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f263,f57])).

fof(f263,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
      | sK0 = k2_relat_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(subsumption_resolution,[],[f258,f54])).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
      | sK0 = k2_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(resolution,[],[f111,f56])).

fof(f111,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ v3_funct_2(X4,X9,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X8,X5)))
      | k2_relat_1(X4) = X5
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X9,X5))) ) ),
    inference(resolution,[],[f109,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_2(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) ) ),
    inference(resolution,[],[f104,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_relat_1(X0,X1)
      | ~ v2_funct_2(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f64,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f254,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,X1,k2_relat_1(X0))
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v3_funct_2(X0,X2,X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(equality_resolution,[],[f249])).

fof(f249,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X2) != X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X3,X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X2) != X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X3,X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f202,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f202,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X2,X0,X1) != X0
      | k6_partfun1(X0) = k5_relat_1(k2_funct_1(X1),X1)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X1,X2,X0)
      | ~ v1_funct_1(X1)
      | ~ v3_funct_2(X1,X3,X4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k6_partfun1(X0) = k5_relat_1(k2_funct_1(X1),X1)
      | k2_relset_1(X2,X0,X1) != X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X1,X2,X0)
      | ~ v1_funct_1(X1)
      | ~ v3_funct_2(X1,X3,X4)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f84,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f596,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f595,f124])).

fof(f124,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f123,f54])).

fof(f123,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f122,f55])).

fof(f122,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f121,f56])).

fof(f121,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f120,f57])).

fof(f120,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f67,f117])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f595,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f594,f148])).

fof(f148,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f147,f54])).

fof(f147,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f146,f55])).

fof(f146,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f145,f56])).

fof(f145,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f144,f57])).

fof(f144,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f70,f117])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f594,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f593,f54])).

fof(f593,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f592,f57])).

fof(f592,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f589,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f589,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f588,f91])).

fof(f588,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f549,f96])).

fof(f549,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f160,f548])).

fof(f548,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f547,f57])).

fof(f547,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f538,f56])).

fof(f538,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(sK1,X0,X1)
      | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f537,f57])).

fof(f537,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
      | ~ v3_funct_2(sK1,X0,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f289,f55])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK1,X0,sK0)
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | k6_partfun1(X0) = k5_relat_1(sK1,k2_funct_1(sK1))
      | ~ v3_funct_2(sK1,X1,X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f288,f54])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK1,X0,sK0)
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | k6_partfun1(X0) = k5_relat_1(sK1,k2_funct_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v3_funct_2(sK1,X1,X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f252,f279])).

fof(f252,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X1,X0,k2_relat_1(X1))
      | k1_xboole_0 = k2_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(X1))))
      | k6_partfun1(X0) = k5_relat_1(X1,k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v3_funct_2(X1,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(equality_resolution,[],[f230])).

fof(f230,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X2) != X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X3,X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X2) != X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X3,X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f185,f77])).

fof(f185,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X1,X0,X2) != X0
      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X1)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X3,X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X1)
      | k2_relset_1(X1,X0,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X3,X4)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f83,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f160,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f159,f54])).

fof(f159,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f158,f57])).

fof(f158,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f157,f124])).

fof(f157,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f154,f148])).

fof(f154,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f119,f88])).

fof(f119,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f118,f117])).

fof(f118,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f58,f117])).

fof(f58,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f117,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f116,f54])).

fof(f116,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f115,f56])).

fof(f115,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f114,f57])).

fof(f114,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f66,f55])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f722,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f721,f54])).

fof(f721,plain,
    ( k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f720,f659])).

fof(f720,plain,
    ( k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f715,f604])).

fof(f604,plain,(
    v3_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f56,f602])).

fof(f715,plain,
    ( k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,sK1)
    | ~ v3_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f603,f373])).

fof(f373,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,X5)
      | ~ v3_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
      | ~ v1_funct_1(X5) ) ),
    inference(backward_demodulation,[],[f360,f363])).

fof(f363,plain,(
    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f358,f93])).

fof(f358,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
      | k6_partfun1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f334,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f334,plain,(
    ! [X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | k6_partfun1(k1_xboole_0) = X14 ) ),
    inference(resolution,[],[f312,f91])).

fof(f312,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | X0 = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    inference(resolution,[],[f256,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f256,plain,(
    ! [X0,X1] :
      ( r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    inference(resolution,[],[f250,f93])).

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | r2_relset_1(X1,X1,X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    inference(resolution,[],[f206,f75])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | r2_relset_1(X1,X1,X2,X0) ) ),
    inference(resolution,[],[f141,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
      | r2_relset_1(X0,X0,X1,X2) ) ),
    inference(resolution,[],[f62,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_relset_1(X0,X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK2(X0,X1,X2)) != k11_relat_1(X2,sK2(X0,X1,X2))
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK2(X0,X1,X2)) != k11_relat_1(X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

fof(f360,plain,(
    ! [X5] :
      ( k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v3_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f334,f70])).

fof(f603,plain,(
    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f55,f602])).

fof(f659,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f605,f363])).

fof(f605,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f57,f602])).

fof(f773,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_funct_1(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_funct_1(sK1)))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f733,f723])).

fof(f733,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_funct_1(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
      | X0 = X1 ) ),
    inference(backward_demodulation,[],[f375,f723])).

fof(f375,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f366,f363])).

fof(f366,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | X0 = X1 ) ),
    inference(backward_demodulation,[],[f312,f363])).

fof(f738,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_funct_1(sK1))) ),
    inference(backward_demodulation,[],[f385,f723])).

fof(f385,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k6_partfun1(k1_xboole_0))) ),
    inference(superposition,[],[f91,f363])).

fof(f1126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | ~ r1_tarski(X1,sK1)
      | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0) ) ),
    inference(forward_demodulation,[],[f1033,f980])).

fof(f1033,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | ~ r1_tarski(X1,k2_funct_1(sK1))
      | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0) ) ),
    inference(backward_demodulation,[],[f776,f980])).

fof(f776,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_funct_1(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_funct_1(sK1)))
      | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0) ) ),
    inference(forward_demodulation,[],[f736,f723])).

fof(f736,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_funct_1(sK1)))
      | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0)
      | ~ r1_tarski(X1,k6_partfun1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f379,f723])).

fof(f379,plain,(
    ! [X0,X1] :
      ( r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
      | ~ r1_tarski(X1,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[],[f374,f75])).

fof(f374,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
      | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0) ) ),
    inference(forward_demodulation,[],[f365,f363])).

fof(f365,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
      | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    inference(backward_demodulation,[],[f256,f363])).

fof(f1243,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK1) ),
    inference(backward_demodulation,[],[f1183,f1242])).

fof(f1242,plain,(
    sK1 = k5_relat_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f1241,f1014])).

fof(f1241,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | sK1 = k5_relat_1(sK1,sK1) ),
    inference(superposition,[],[f1237,f1011])).

fof(f1011,plain,(
    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f726,f980])).

fof(f726,plain,(
    k2_funct_1(sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f363,f723])).

fof(f1237,plain,(
    ! [X17] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X17)))
      | sK1 = k5_relat_1(sK1,sK1) ) ),
    inference(resolution,[],[f1037,f54])).

fof(f1037,plain,(
    ! [X21,X22] :
      ( ~ v1_funct_1(X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22)))
      | sK1 = k5_relat_1(X21,sK1) ) ),
    inference(backward_demodulation,[],[f781,f980])).

fof(f781,plain,(
    ! [X21,X22] :
      ( k2_funct_1(sK1) = k5_relat_1(X21,k2_funct_1(sK1))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22)))
      | ~ v1_funct_1(X21) ) ),
    inference(forward_demodulation,[],[f780,f723])).

fof(f780,plain,(
    ! [X21,X22] :
      ( k6_partfun1(k1_xboole_0) = k5_relat_1(X21,k6_partfun1(k1_xboole_0))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22)))
      | ~ v1_funct_1(X21) ) ),
    inference(subsumption_resolution,[],[f746,f124])).

fof(f746,plain,(
    ! [X21,X22] :
      ( ~ v1_funct_1(k2_funct_1(sK1))
      | k6_partfun1(k1_xboole_0) = k5_relat_1(X21,k6_partfun1(k1_xboole_0))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22)))
      | ~ v1_funct_1(X21) ) ),
    inference(backward_demodulation,[],[f568,f723])).

fof(f568,plain,(
    ! [X21,X22] :
      ( k6_partfun1(k1_xboole_0) = k5_relat_1(X21,k6_partfun1(k1_xboole_0))
      | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22)))
      | ~ v1_funct_1(X21) ) ),
    inference(resolution,[],[f361,f91])).

fof(f361,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,k1_xboole_0)))
      | k6_partfun1(k1_xboole_0) = k5_relat_1(X6,X7)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9)))
      | ~ v1_funct_1(X6) ) ),
    inference(resolution,[],[f334,f164])).

fof(f164,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f90,f88])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1183,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f1182,f1014])).

fof(f1182,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f1181,f1011])).

fof(f1181,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f1180,f54])).

fof(f1180,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f1179])).

fof(f1179,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f1133,f88])).

fof(f1133,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f1132])).

fof(f1132,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1),sK1)
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f1040,f980])).

fof(f1040,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1),sK1)
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f786,f980])).

fof(f786,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)),k2_funct_1(sK1))
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f754,f723])).

fof(f754,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)),k2_funct_1(sK1))
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f666,f723])).

fof(f666,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0))
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)),k6_partfun1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f609,f602])).

fof(f609,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)),k6_partfun1(k1_xboole_0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f119,f602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:18:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (17616)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (17588)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (17589)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (17591)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (17592)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (17598)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (17611)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (17618)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (17605)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (17593)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (17609)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (17587)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (17594)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (17600)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (17612)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (17599)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (17606)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (17613)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (17604)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (17617)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (17601)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (17602)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (17597)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (17596)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (17607)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (17608)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (17614)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (17619)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (17603)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (17605)Refutation not found, incomplete strategy% (17605)------------------------------
% 0.21/0.54  % (17605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17605)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17605)Memory used [KB]: 10746
% 0.21/0.54  % (17605)Time elapsed: 0.139 s
% 0.21/0.54  % (17605)------------------------------
% 0.21/0.54  % (17605)------------------------------
% 0.21/0.54  % (17610)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.16/0.65  % (17611)Refutation found. Thanks to Tanya!
% 2.16/0.65  % SZS status Theorem for theBenchmark
% 2.16/0.65  % (17714)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.67  % SZS output start Proof for theBenchmark
% 2.16/0.67  fof(f1244,plain,(
% 2.16/0.67    $false),
% 2.16/0.67    inference(subsumption_resolution,[],[f1243,f1216])).
% 2.16/0.67  fof(f1216,plain,(
% 2.16/0.67    r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK1)),
% 2.16/0.67    inference(resolution,[],[f1215,f93])).
% 2.16/0.67  fof(f93,plain,(
% 2.16/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.16/0.67    inference(equality_resolution,[],[f72])).
% 2.16/0.67  fof(f72,plain,(
% 2.16/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.16/0.67    inference(cnf_transformation,[],[f51])).
% 2.16/0.67  fof(f51,plain,(
% 2.16/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/0.67    inference(flattening,[],[f50])).
% 2.16/0.67  fof(f50,plain,(
% 2.16/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/0.67    inference(nnf_transformation,[],[f2])).
% 2.16/0.67  fof(f2,axiom,(
% 2.16/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.16/0.67  fof(f1215,plain,(
% 2.16/0.67    ( ! [X2] : (~r1_tarski(X2,sK1) | r2_relset_1(k1_xboole_0,k1_xboole_0,X2,sK1)) )),
% 2.16/0.67    inference(resolution,[],[f1126,f1014])).
% 2.16/0.67  fof(f1014,plain,(
% 2.16/0.67    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 2.16/0.67    inference(backward_demodulation,[],[f738,f980])).
% 2.16/0.67  fof(f980,plain,(
% 2.16/0.67    sK1 = k2_funct_1(sK1)),
% 2.16/0.67    inference(resolution,[],[f978,f738])).
% 2.16/0.67  fof(f978,plain,(
% 2.16/0.67    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_funct_1(sK1))) | sK1 = X5) )),
% 2.16/0.67    inference(resolution,[],[f773,f751])).
% 2.16/0.67  fof(f751,plain,(
% 2.16/0.67    m1_subset_1(sK1,k1_zfmisc_1(k2_funct_1(sK1)))),
% 2.16/0.67    inference(backward_demodulation,[],[f659,f723])).
% 2.16/0.67  fof(f723,plain,(
% 2.16/0.67    k2_funct_1(sK1) = k6_partfun1(k1_xboole_0)),
% 2.16/0.67    inference(forward_demodulation,[],[f722,f608])).
% 2.16/0.67  fof(f608,plain,(
% 2.16/0.67    k2_funct_1(sK1) = k2_funct_2(k1_xboole_0,sK1)),
% 2.16/0.67    inference(backward_demodulation,[],[f117,f602])).
% 2.16/0.67  fof(f602,plain,(
% 2.16/0.67    k1_xboole_0 = sK0),
% 2.16/0.67    inference(subsumption_resolution,[],[f601,f91])).
% 2.16/0.67  fof(f91,plain,(
% 2.16/0.67    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.16/0.67    inference(definition_unfolding,[],[f61,f60])).
% 2.16/0.67  fof(f60,plain,(
% 2.16/0.67    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f17])).
% 2.16/0.67  fof(f17,axiom,(
% 2.16/0.67    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.16/0.67  fof(f61,plain,(
% 2.16/0.67    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f9])).
% 2.16/0.67  fof(f9,axiom,(
% 2.16/0.67    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.16/0.67  fof(f601,plain,(
% 2.16/0.67    k1_xboole_0 = sK0 | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.67    inference(resolution,[],[f598,f96])).
% 2.16/0.67  fof(f96,plain,(
% 2.16/0.67    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f95])).
% 2.16/0.67  fof(f95,plain,(
% 2.16/0.67    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(equality_resolution,[],[f87])).
% 2.16/0.67  fof(f87,plain,(
% 2.16/0.67    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f53])).
% 2.16/0.67  fof(f53,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(nnf_transformation,[],[f40])).
% 2.16/0.67  fof(f40,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(flattening,[],[f39])).
% 2.16/0.67  fof(f39,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.16/0.67    inference(ennf_transformation,[],[f8])).
% 2.16/0.67  fof(f8,axiom,(
% 2.16/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.16/0.67  fof(f598,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | k1_xboole_0 = sK0),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f597])).
% 2.16/0.67  fof(f597,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 2.16/0.67    inference(superposition,[],[f596,f575])).
% 2.16/0.67  fof(f575,plain,(
% 2.16/0.67    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | k1_xboole_0 = sK0),
% 2.16/0.67    inference(subsumption_resolution,[],[f574,f57])).
% 2.16/0.67  fof(f57,plain,(
% 2.16/0.67    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.67    inference(cnf_transformation,[],[f46])).
% 2.16/0.67  fof(f46,plain,(
% 2.16/0.67    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.16/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f45])).
% 2.16/0.67  fof(f45,plain,(
% 2.16/0.67    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.16/0.67    introduced(choice_axiom,[])).
% 2.16/0.67  fof(f22,plain,(
% 2.16/0.67    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.16/0.67    inference(flattening,[],[f21])).
% 2.16/0.67  fof(f21,plain,(
% 2.16/0.67    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.16/0.67    inference(ennf_transformation,[],[f20])).
% 2.16/0.67  fof(f20,negated_conjecture,(
% 2.16/0.67    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.16/0.67    inference(negated_conjecture,[],[f19])).
% 2.16/0.67  fof(f19,conjecture,(
% 2.16/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 2.16/0.67  fof(f574,plain,(
% 2.16/0.67    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.67    inference(resolution,[],[f541,f56])).
% 2.16/0.67  fof(f56,plain,(
% 2.16/0.67    v3_funct_2(sK1,sK0,sK0)),
% 2.16/0.67    inference(cnf_transformation,[],[f46])).
% 2.16/0.67  fof(f541,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v3_funct_2(sK1,X0,X1) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f540,f57])).
% 2.16/0.67  fof(f540,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v3_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(resolution,[],[f295,f55])).
% 2.16/0.67  fof(f55,plain,(
% 2.16/0.67    v1_funct_2(sK1,sK0,sK0)),
% 2.16/0.67    inference(cnf_transformation,[],[f46])).
% 2.16/0.67  fof(f295,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X0,sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v3_funct_2(sK1,X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f294,f54])).
% 2.16/0.67  fof(f54,plain,(
% 2.16/0.67    v1_funct_1(sK1)),
% 2.16/0.67    inference(cnf_transformation,[],[f46])).
% 2.16/0.67  fof(f294,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X0,sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v1_funct_1(sK1) | ~v3_funct_2(sK1,X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.16/0.67    inference(superposition,[],[f254,f279])).
% 2.16/0.67  fof(f279,plain,(
% 2.16/0.67    sK0 = k2_relat_1(sK1)),
% 2.16/0.67    inference(resolution,[],[f273,f57])).
% 2.16/0.67  fof(f273,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK0 = k2_relat_1(sK1)) )),
% 2.16/0.67    inference(resolution,[],[f264,f57])).
% 2.16/0.67  fof(f264,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK0 = k2_relat_1(sK1)) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f263,f57])).
% 2.16/0.67  fof(f263,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | sK0 = k2_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f258,f54])).
% 2.16/0.67  fof(f258,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | sK0 = k2_relat_1(sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) )),
% 2.16/0.67    inference(resolution,[],[f111,f56])).
% 2.16/0.67  fof(f111,plain,(
% 2.16/0.67    ( ! [X6,X4,X8,X7,X5,X9] : (~v3_funct_2(X4,X9,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X8,X5))) | k2_relat_1(X4) = X5 | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X9,X5)))) )),
% 2.16/0.67    inference(resolution,[],[f109,f82])).
% 2.16/0.67  fof(f82,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f35])).
% 2.16/0.67  fof(f35,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(flattening,[],[f34])).
% 2.16/0.67  fof(f34,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f11])).
% 2.16/0.67  fof(f11,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 2.16/0.67  fof(f109,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_2(X0,X1) | k2_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))) )),
% 2.16/0.67    inference(resolution,[],[f104,f79])).
% 2.16/0.67  fof(f79,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f33])).
% 2.16/0.67  fof(f33,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f6])).
% 2.16/0.67  fof(f6,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.16/0.67  fof(f104,plain,(
% 2.16/0.67    ( ! [X2,X0,X3,X1] : (~v5_relat_1(X0,X1) | ~v2_funct_2(X0,X1) | k2_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.16/0.67    inference(resolution,[],[f64,f76])).
% 2.16/0.67  fof(f76,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f31])).
% 2.16/0.67  fof(f31,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f5])).
% 2.16/0.67  fof(f5,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.16/0.67  fof(f64,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0) )),
% 2.16/0.67    inference(cnf_transformation,[],[f49])).
% 2.16/0.67  fof(f49,plain,(
% 2.16/0.67    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.16/0.67    inference(nnf_transformation,[],[f26])).
% 2.16/0.67  fof(f26,plain,(
% 2.16/0.67    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.16/0.67    inference(flattening,[],[f25])).
% 2.16/0.67  fof(f25,plain,(
% 2.16/0.67    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.16/0.67    inference(ennf_transformation,[],[f12])).
% 2.16/0.67  fof(f12,axiom,(
% 2.16/0.67    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 2.16/0.67  fof(f254,plain,(
% 2.16/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,X1,k2_relat_1(X0)) | k1_xboole_0 = k2_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v3_funct_2(X0,X2,X3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.16/0.67    inference(equality_resolution,[],[f249])).
% 2.16/0.67  fof(f249,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X3,X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f248])).
% 2.16/0.67  fof(f248,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X3,X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(superposition,[],[f202,f77])).
% 2.16/0.67  fof(f77,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f32])).
% 2.16/0.67  fof(f32,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f7])).
% 2.16/0.67  fof(f7,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.16/0.67  fof(f202,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X2,X0,X1) != X0 | k6_partfun1(X0) = k5_relat_1(k2_funct_1(X1),X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1) | ~v3_funct_2(X1,X3,X4) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f201])).
% 2.16/0.67  fof(f201,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k6_partfun1(X0) = k5_relat_1(k2_funct_1(X1),X1) | k2_relset_1(X2,X0,X1) != X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1) | ~v3_funct_2(X1,X3,X4) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.16/0.67    inference(resolution,[],[f84,f81])).
% 2.16/0.67  fof(f81,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f35])).
% 2.16/0.67  fof(f84,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f37])).
% 2.16/0.67  fof(f37,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.16/0.67    inference(flattening,[],[f36])).
% 2.16/0.67  fof(f36,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.16/0.67    inference(ennf_transformation,[],[f18])).
% 2.16/0.67  fof(f18,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.16/0.67  fof(f596,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | k1_xboole_0 = sK0),
% 2.16/0.67    inference(subsumption_resolution,[],[f595,f124])).
% 2.16/0.67  fof(f124,plain,(
% 2.16/0.67    v1_funct_1(k2_funct_1(sK1))),
% 2.16/0.67    inference(subsumption_resolution,[],[f123,f54])).
% 2.16/0.67  fof(f123,plain,(
% 2.16/0.67    v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f122,f55])).
% 2.16/0.67  fof(f122,plain,(
% 2.16/0.67    v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f121,f56])).
% 2.16/0.67  fof(f121,plain,(
% 2.16/0.67    v1_funct_1(k2_funct_1(sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f120,f57])).
% 2.16/0.67  fof(f120,plain,(
% 2.16/0.67    v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(superposition,[],[f67,f117])).
% 2.16/0.67  fof(f67,plain,(
% 2.16/0.67    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f30])).
% 2.16/0.67  fof(f30,plain,(
% 2.16/0.67    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.16/0.67    inference(flattening,[],[f29])).
% 2.16/0.67  fof(f29,plain,(
% 2.16/0.67    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.16/0.67    inference(ennf_transformation,[],[f14])).
% 2.16/0.67  fof(f14,axiom,(
% 2.16/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 2.16/0.67  fof(f595,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | ~v1_funct_1(k2_funct_1(sK1))),
% 2.16/0.67    inference(subsumption_resolution,[],[f594,f148])).
% 2.16/0.67  fof(f148,plain,(
% 2.16/0.67    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.67    inference(subsumption_resolution,[],[f147,f54])).
% 2.16/0.67  fof(f147,plain,(
% 2.16/0.67    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f146,f55])).
% 2.16/0.67  fof(f146,plain,(
% 2.16/0.67    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f145,f56])).
% 2.16/0.67  fof(f145,plain,(
% 2.16/0.67    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f144,f57])).
% 2.16/0.67  fof(f144,plain,(
% 2.16/0.67    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(superposition,[],[f70,f117])).
% 2.16/0.67  fof(f70,plain,(
% 2.16/0.67    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f30])).
% 2.16/0.67  fof(f594,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 2.16/0.67    inference(subsumption_resolution,[],[f593,f54])).
% 2.16/0.67  fof(f593,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 2.16/0.67    inference(subsumption_resolution,[],[f592,f57])).
% 2.16/0.67  fof(f592,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 2.16/0.67    inference(superposition,[],[f589,f88])).
% 2.16/0.67  fof(f88,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f42])).
% 2.16/0.67  fof(f42,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.16/0.67    inference(flattening,[],[f41])).
% 2.16/0.67  fof(f41,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.16/0.67    inference(ennf_transformation,[],[f15])).
% 2.16/0.67  fof(f15,axiom,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.16/0.67  fof(f589,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | k1_xboole_0 = sK0),
% 2.16/0.67    inference(subsumption_resolution,[],[f588,f91])).
% 2.16/0.67  fof(f588,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.67    inference(resolution,[],[f549,f96])).
% 2.16/0.67  fof(f549,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | k1_xboole_0 = sK0),
% 2.16/0.67    inference(superposition,[],[f160,f548])).
% 2.16/0.67  fof(f548,plain,(
% 2.16/0.67    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0),
% 2.16/0.67    inference(subsumption_resolution,[],[f547,f57])).
% 2.16/0.67  fof(f547,plain,(
% 2.16/0.67    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.67    inference(resolution,[],[f538,f56])).
% 2.16/0.67  fof(f538,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v3_funct_2(sK1,X0,X1) | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f537,f57])).
% 2.16/0.67  fof(f537,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v3_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(resolution,[],[f289,f55])).
% 2.16/0.67  fof(f289,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X0,sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | k6_partfun1(X0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v3_funct_2(sK1,X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f288,f54])).
% 2.16/0.67  fof(f288,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X0,sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | k6_partfun1(X0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v3_funct_2(sK1,X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.16/0.67    inference(superposition,[],[f252,f279])).
% 2.16/0.67  fof(f252,plain,(
% 2.16/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X1,X0,k2_relat_1(X1)) | k1_xboole_0 = k2_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(X1)))) | k6_partfun1(X0) = k5_relat_1(X1,k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v3_funct_2(X1,X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.16/0.67    inference(equality_resolution,[],[f230])).
% 2.16/0.67  fof(f230,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X3,X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f229])).
% 2.16/0.67  fof(f229,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X3,X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(superposition,[],[f185,f77])).
% 2.16/0.67  fof(f185,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X1,X0,X2) != X0 | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X3,X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f184])).
% 2.16/0.67  fof(f184,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X1) | k2_relset_1(X1,X0,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X3,X4) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.16/0.67    inference(resolution,[],[f83,f81])).
% 2.16/0.67  fof(f83,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f37])).
% 2.16/0.67  fof(f160,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 2.16/0.67    inference(subsumption_resolution,[],[f159,f54])).
% 2.16/0.67  fof(f159,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f158,f57])).
% 2.16/0.67  fof(f158,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f157,f124])).
% 2.16/0.67  fof(f157,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f154,f148])).
% 2.16/0.67  fof(f154,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(superposition,[],[f119,f88])).
% 2.16/0.67  fof(f119,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 2.16/0.67    inference(forward_demodulation,[],[f118,f117])).
% 2.16/0.67  fof(f118,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 2.16/0.67    inference(backward_demodulation,[],[f58,f117])).
% 2.16/0.67  fof(f58,plain,(
% 2.16/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 2.16/0.67    inference(cnf_transformation,[],[f46])).
% 2.16/0.67  fof(f117,plain,(
% 2.16/0.67    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f116,f54])).
% 2.16/0.67  fof(f116,plain,(
% 2.16/0.67    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f115,f56])).
% 2.16/0.67  fof(f115,plain,(
% 2.16/0.67    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f114,f57])).
% 2.16/0.67  fof(f114,plain,(
% 2.16/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(resolution,[],[f66,f55])).
% 2.16/0.67  fof(f66,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f28])).
% 2.16/0.67  fof(f28,plain,(
% 2.16/0.67    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.16/0.67    inference(flattening,[],[f27])).
% 2.16/0.67  fof(f27,plain,(
% 2.16/0.67    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.16/0.67    inference(ennf_transformation,[],[f16])).
% 2.16/0.67  fof(f16,axiom,(
% 2.16/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 2.16/0.67  fof(f722,plain,(
% 2.16/0.67    k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f721,f54])).
% 2.16/0.67  fof(f721,plain,(
% 2.16/0.67    k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,sK1) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f720,f659])).
% 2.16/0.67  fof(f720,plain,(
% 2.16/0.67    k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f715,f604])).
% 2.16/0.67  fof(f604,plain,(
% 2.16/0.67    v3_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 2.16/0.67    inference(backward_demodulation,[],[f56,f602])).
% 2.16/0.67  fof(f715,plain,(
% 2.16/0.67    k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,sK1) | ~v3_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(resolution,[],[f603,f373])).
% 2.16/0.67  fof(f373,plain,(
% 2.16/0.67    ( ! [X5] : (~v1_funct_2(X5,k1_xboole_0,k1_xboole_0) | k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,X5) | ~v3_funct_2(X5,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X5,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | ~v1_funct_1(X5)) )),
% 2.16/0.67    inference(backward_demodulation,[],[f360,f363])).
% 2.16/0.67  fof(f363,plain,(
% 2.16/0.67    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0)),
% 2.16/0.67    inference(resolution,[],[f358,f93])).
% 2.16/0.67  fof(f358,plain,(
% 2.16/0.67    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | k6_partfun1(k1_xboole_0) = X0) )),
% 2.16/0.67    inference(resolution,[],[f334,f75])).
% 2.16/0.67  fof(f75,plain,(
% 2.16/0.67    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f52])).
% 2.16/0.67  fof(f52,plain,(
% 2.16/0.67    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.16/0.67    inference(nnf_transformation,[],[f3])).
% 2.16/0.67  fof(f3,axiom,(
% 2.16/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.16/0.67  fof(f334,plain,(
% 2.16/0.67    ( ! [X14] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k6_partfun1(k1_xboole_0) = X14) )),
% 2.16/0.67    inference(resolution,[],[f312,f91])).
% 2.16/0.67  fof(f312,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | X0 = X1) )),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f311])).
% 2.16/0.67  fof(f311,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | X0 = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) )),
% 2.16/0.67    inference(resolution,[],[f256,f86])).
% 2.16/0.67  fof(f86,plain,(
% 2.16/0.67    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f53])).
% 2.16/0.67  fof(f256,plain,(
% 2.16/0.67    ( ! [X0,X1] : (r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) )),
% 2.16/0.67    inference(resolution,[],[f250,f93])).
% 2.16/0.67  fof(f250,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | r2_relset_1(X1,X1,X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))) )),
% 2.16/0.67    inference(resolution,[],[f206,f75])).
% 2.16/0.67  fof(f206,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | r2_relset_1(X1,X1,X2,X0)) )),
% 2.16/0.67    inference(resolution,[],[f141,f59])).
% 2.16/0.67  fof(f59,plain,(
% 2.16/0.67    v1_xboole_0(k1_xboole_0)),
% 2.16/0.67    inference(cnf_transformation,[],[f1])).
% 2.16/0.67  fof(f1,axiom,(
% 2.16/0.67    v1_xboole_0(k1_xboole_0)),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.16/0.67  fof(f141,plain,(
% 2.16/0.67    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | r2_relset_1(X0,X0,X1,X2)) )),
% 2.16/0.67    inference(resolution,[],[f62,f85])).
% 2.16/0.67  fof(f85,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f38])).
% 2.16/0.67  fof(f38,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.16/0.67    inference(ennf_transformation,[],[f4])).
% 2.16/0.67  fof(f4,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 2.16/0.67  fof(f62,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_relset_1(X0,X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f48])).
% 2.16/0.67  fof(f48,plain,(
% 2.16/0.67    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | (k11_relat_1(X1,sK2(X0,X1,X2)) != k11_relat_1(X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 2.16/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f47])).
% 2.16/0.67  fof(f47,plain,(
% 2.16/0.67    ! [X2,X1,X0] : (? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) => (k11_relat_1(X1,sK2(X0,X1,X2)) != k11_relat_1(X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X0)))),
% 2.16/0.67    introduced(choice_axiom,[])).
% 2.16/0.67  fof(f24,plain,(
% 2.16/0.67    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 2.16/0.67    inference(flattening,[],[f23])).
% 2.16/0.67  fof(f23,plain,(
% 2.16/0.67    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 2.16/0.67    inference(ennf_transformation,[],[f10])).
% 2.16/0.67  fof(f10,axiom,(
% 2.16/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).
% 2.16/0.67  fof(f360,plain,(
% 2.16/0.67    ( ! [X5] : (k6_partfun1(k1_xboole_0) = k2_funct_2(k1_xboole_0,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_funct_2(X5,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(X5,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(X5)) )),
% 2.16/0.67    inference(resolution,[],[f334,f70])).
% 2.16/0.67  fof(f603,plain,(
% 2.16/0.67    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 2.16/0.67    inference(backward_demodulation,[],[f55,f602])).
% 2.16/0.67  fof(f659,plain,(
% 2.16/0.67    m1_subset_1(sK1,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))),
% 2.16/0.67    inference(forward_demodulation,[],[f605,f363])).
% 2.16/0.67  fof(f605,plain,(
% 2.16/0.67    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.16/0.67    inference(backward_demodulation,[],[f57,f602])).
% 2.16/0.67  fof(f773,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_funct_1(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_funct_1(sK1))) | X0 = X1) )),
% 2.16/0.67    inference(forward_demodulation,[],[f733,f723])).
% 2.16/0.67  fof(f733,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_funct_1(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | X0 = X1) )),
% 2.16/0.67    inference(backward_demodulation,[],[f375,f723])).
% 2.16/0.67  fof(f375,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | ~m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | X0 = X1) )),
% 2.16/0.67    inference(forward_demodulation,[],[f366,f363])).
% 2.16/0.67  fof(f366,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | X0 = X1) )),
% 2.16/0.67    inference(backward_demodulation,[],[f312,f363])).
% 2.16/0.67  fof(f738,plain,(
% 2.16/0.67    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_funct_1(sK1)))),
% 2.16/0.67    inference(backward_demodulation,[],[f385,f723])).
% 2.16/0.67  fof(f385,plain,(
% 2.16/0.67    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k6_partfun1(k1_xboole_0)))),
% 2.16/0.67    inference(superposition,[],[f91,f363])).
% 2.16/0.67  fof(f1126,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r1_tarski(X1,sK1) | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0)) )),
% 2.16/0.67    inference(forward_demodulation,[],[f1033,f980])).
% 2.16/0.67  fof(f1033,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r1_tarski(X1,k2_funct_1(sK1)) | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0)) )),
% 2.16/0.67    inference(backward_demodulation,[],[f776,f980])).
% 2.16/0.67  fof(f776,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~r1_tarski(X1,k2_funct_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_funct_1(sK1))) | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0)) )),
% 2.16/0.67    inference(forward_demodulation,[],[f736,f723])).
% 2.16/0.67  fof(f736,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_funct_1(sK1))) | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0) | ~r1_tarski(X1,k6_partfun1(k1_xboole_0))) )),
% 2.16/0.67    inference(backward_demodulation,[],[f379,f723])).
% 2.16/0.67  fof(f379,plain,(
% 2.16/0.67    ( ! [X0,X1] : (r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | ~r1_tarski(X1,k6_partfun1(k1_xboole_0))) )),
% 2.16/0.67    inference(resolution,[],[f374,f75])).
% 2.16/0.67  fof(f374,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | ~m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0)) )),
% 2.16/0.67    inference(forward_demodulation,[],[f365,f363])).
% 2.16/0.67  fof(f365,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) )),
% 2.16/0.67    inference(backward_demodulation,[],[f256,f363])).
% 2.16/0.67  fof(f1243,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK1)),
% 2.16/0.67    inference(backward_demodulation,[],[f1183,f1242])).
% 2.16/0.67  fof(f1242,plain,(
% 2.16/0.67    sK1 = k5_relat_1(sK1,sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f1241,f1014])).
% 2.16/0.67  fof(f1241,plain,(
% 2.16/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | sK1 = k5_relat_1(sK1,sK1)),
% 2.16/0.67    inference(superposition,[],[f1237,f1011])).
% 2.16/0.67  fof(f1011,plain,(
% 2.16/0.67    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 2.16/0.67    inference(backward_demodulation,[],[f726,f980])).
% 2.16/0.67  fof(f726,plain,(
% 2.16/0.67    k2_funct_1(sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 2.16/0.67    inference(backward_demodulation,[],[f363,f723])).
% 2.16/0.67  fof(f1237,plain,(
% 2.16/0.67    ( ! [X17] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X17))) | sK1 = k5_relat_1(sK1,sK1)) )),
% 2.16/0.67    inference(resolution,[],[f1037,f54])).
% 2.16/0.67  fof(f1037,plain,(
% 2.16/0.67    ( ! [X21,X22] : (~v1_funct_1(X21) | ~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22))) | sK1 = k5_relat_1(X21,sK1)) )),
% 2.16/0.67    inference(backward_demodulation,[],[f781,f980])).
% 2.16/0.67  fof(f781,plain,(
% 2.16/0.67    ( ! [X21,X22] : (k2_funct_1(sK1) = k5_relat_1(X21,k2_funct_1(sK1)) | ~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22))) | ~v1_funct_1(X21)) )),
% 2.16/0.67    inference(forward_demodulation,[],[f780,f723])).
% 2.16/0.67  fof(f780,plain,(
% 2.16/0.67    ( ! [X21,X22] : (k6_partfun1(k1_xboole_0) = k5_relat_1(X21,k6_partfun1(k1_xboole_0)) | ~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22))) | ~v1_funct_1(X21)) )),
% 2.16/0.67    inference(subsumption_resolution,[],[f746,f124])).
% 2.16/0.67  fof(f746,plain,(
% 2.16/0.67    ( ! [X21,X22] : (~v1_funct_1(k2_funct_1(sK1)) | k6_partfun1(k1_xboole_0) = k5_relat_1(X21,k6_partfun1(k1_xboole_0)) | ~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22))) | ~v1_funct_1(X21)) )),
% 2.16/0.67    inference(backward_demodulation,[],[f568,f723])).
% 2.16/0.67  fof(f568,plain,(
% 2.16/0.67    ( ! [X21,X22] : (k6_partfun1(k1_xboole_0) = k5_relat_1(X21,k6_partfun1(k1_xboole_0)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X22))) | ~v1_funct_1(X21)) )),
% 2.16/0.67    inference(resolution,[],[f361,f91])).
% 2.16/0.67  fof(f361,plain,(
% 2.16/0.67    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,k1_xboole_0))) | k6_partfun1(k1_xboole_0) = k5_relat_1(X6,X7) | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9))) | ~v1_funct_1(X6)) )),
% 2.16/0.67    inference(resolution,[],[f334,f164])).
% 2.16/0.67  fof(f164,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f163])).
% 2.16/0.67  fof(f163,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.16/0.67    inference(superposition,[],[f90,f88])).
% 2.16/0.67  fof(f90,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f44])).
% 2.16/0.67  fof(f44,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.16/0.67    inference(flattening,[],[f43])).
% 2.16/0.67  fof(f43,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.16/0.67    inference(ennf_transformation,[],[f13])).
% 2.16/0.67  fof(f13,axiom,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.16/0.67  fof(f1183,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1)),
% 2.16/0.67    inference(subsumption_resolution,[],[f1182,f1014])).
% 2.16/0.67  fof(f1182,plain,(
% 2.16/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1)),
% 2.16/0.67    inference(forward_demodulation,[],[f1181,f1011])).
% 2.16/0.67  fof(f1181,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.16/0.67    inference(subsumption_resolution,[],[f1180,f54])).
% 2.16/0.67  fof(f1180,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f1179])).
% 2.16/0.67  fof(f1179,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK1)),
% 2.16/0.67    inference(superposition,[],[f1133,f88])).
% 2.16/0.67  fof(f1133,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1),sK1)),
% 2.16/0.67    inference(duplicate_literal_removal,[],[f1132])).
% 2.16/0.67  fof(f1132,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1),sK1) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1),sK1)),
% 2.16/0.67    inference(forward_demodulation,[],[f1040,f980])).
% 2.16/0.67  fof(f1040,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1),sK1) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k2_funct_1(sK1))),
% 2.16/0.67    inference(backward_demodulation,[],[f786,f980])).
% 2.16/0.67  fof(f786,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)),k2_funct_1(sK1)) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k2_funct_1(sK1))),
% 2.16/0.67    inference(forward_demodulation,[],[f754,f723])).
% 2.16/0.67  fof(f754,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)),k2_funct_1(sK1)) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0))),
% 2.16/0.67    inference(backward_demodulation,[],[f666,f723])).
% 2.16/0.67  fof(f666,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1),k6_partfun1(k1_xboole_0)) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)),k6_partfun1(k1_xboole_0))),
% 2.16/0.67    inference(forward_demodulation,[],[f609,f602])).
% 2.16/0.67  fof(f609,plain,(
% 2.16/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)),k6_partfun1(k1_xboole_0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 2.16/0.67    inference(backward_demodulation,[],[f119,f602])).
% 2.16/0.67  % SZS output end Proof for theBenchmark
% 2.16/0.67  % (17611)------------------------------
% 2.16/0.67  % (17611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (17611)Termination reason: Refutation
% 2.16/0.67  
% 2.16/0.67  % (17611)Memory used [KB]: 7164
% 2.16/0.67  % (17611)Time elapsed: 0.251 s
% 2.16/0.67  % (17611)------------------------------
% 2.16/0.67  % (17611)------------------------------
% 2.16/0.68  % (17584)Success in time 0.315 s
%------------------------------------------------------------------------------
