%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t8_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:53 EDT 2019

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  153 (7010 expanded)
%              Number of leaves         :   13 (1680 expanded)
%              Depth                    :   32
%              Number of atoms          :  432 (43524 expanded)
%              Number of equality atoms :  203 (11332 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11163,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9980,f9302])).

fof(f9302,plain,(
    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(trivial_inequality_removal,[],[f8721])).

fof(f8721,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f8197,f5785])).

fof(f5785,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f4874,f4203])).

fof(f4203,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f4182,f815])).

fof(f815,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(superposition,[],[f238,f401])).

fof(f401,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f400,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f52])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',t8_funct_2)).

fof(f400,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f393,f99])).

fof(f99,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f61,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',cc1_relset_1)).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f393,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f181,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',t65_relat_1)).

fof(f181,plain,
    ( k1_relat_1(sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f180,f61])).

fof(f180,plain,
    ( k1_relat_1(sK3) = sK0
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f175,f60])).

fof(f60,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f175,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f100,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',d1_funct_2)).

fof(f100,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f61,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',redefinition_k1_relset_1)).

fof(f238,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f117,f142])).

fof(f142,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(resolution,[],[f112,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',t3_subset)).

fof(f112,plain,(
    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f102,f100])).

fof(f102,plain,(
    m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',dt_k1_relset_1)).

fof(f117,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(subsumption_resolution,[],[f114,f99])).

fof(f114,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f111,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',t11_relset_1)).

fof(f111,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f101,f62])).

fof(f62,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f61,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',redefinition_k2_relset_1)).

fof(f4182,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(resolution,[],[f822,f95])).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f822,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f808,f238])).

fof(f808,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(superposition,[],[f136,f401])).

fof(f136,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f64,f59])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f64,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f4874,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f4873,f1699])).

fof(f1699,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1695,f401])).

fof(f1695,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(superposition,[],[f857,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(resolution,[],[f99,f67])).

fof(f857,plain,
    ( k1_relat_1(sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f856,f340])).

fof(f340,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(subsumption_resolution,[],[f329,f245])).

fof(f245,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f244,f238])).

fof(f244,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f136,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f329,plain,
    ( k1_relset_1(sK0,sK2,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f238,f84])).

fof(f856,plain,
    ( k1_relat_1(sK3) != sK0
    | v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f854,f238])).

fof(f854,plain,
    ( k1_relat_1(sK3) != sK0
    | v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f86,f325])).

fof(f325,plain,(
    k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f238,f80])).

fof(f4873,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f4868,f99])).

fof(f4868,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f4867])).

fof(f4867,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f66,f4673])).

fof(f4673,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f4338,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',t6_boole)).

fof(f4338,plain,
    ( v1_xboole_0(k1_relat_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f4330])).

fof(f4330,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | v1_xboole_0(k1_relat_1(sK3)) ),
    inference(superposition,[],[f857,f4284])).

fof(f4284,plain,
    ( k1_relat_1(sK3) = sK0
    | v1_xboole_0(k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f4283,f100])).

fof(f4283,plain,
    ( v1_xboole_0(k1_relat_1(sK3))
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(trivial_inequality_removal,[],[f4282])).

fof(f4282,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_xboole_0(k1_relat_1(sK3))
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(superposition,[],[f4255,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(subsumption_resolution,[],[f97,f61])).

fof(f97,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f60,f84])).

fof(f4255,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(k1_relat_1(sK3)) ),
    inference(resolution,[],[f2859,f65])).

fof(f65,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',dt_o_0_0_xboole_0)).

fof(f2859,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(sK3))
      | k1_xboole_0 != sK1 ) ),
    inference(duplicate_literal_removal,[],[f2858])).

fof(f2858,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(sK3))
      | k1_xboole_0 != sK1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f192,f68])).

fof(f192,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_relat_1(sK3))
    | k1_xboole_0 != sK1 ),
    inference(superposition,[],[f143,f63])).

fof(f143,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(k1_relat_1(sK3)) ),
    inference(resolution,[],[f112,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t8_funct_2.p',cc1_subset_1)).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f8197,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f8137,f68])).

fof(f8137,plain,(
    v1_xboole_0(k2_relat_1(sK3)) ),
    inference(resolution,[],[f8083,f65])).

fof(f8083,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(sK3)) ) ),
    inference(duplicate_literal_removal,[],[f8082])).

fof(f8082,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(sK3))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f4883,f68])).

fof(f4883,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f4874,f164])).

fof(f164,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(k2_relat_1(sK3)) ),
    inference(resolution,[],[f115,f69])).

fof(f115,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f111,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f9980,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f9729,f6481])).

fof(f6481,plain,(
    k1_relset_1(sK0,k1_xboole_0,sK3) = sK0 ),
    inference(subsumption_resolution,[],[f6042,f5813])).

fof(f5813,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f4898,f122])).

fof(f122,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f120])).

fof(f120,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(superposition,[],[f60,f63])).

fof(f4898,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f4874,f246])).

fof(f246,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f243,f238])).

fof(f243,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 != sK1 ),
    inference(superposition,[],[f136,f63])).

fof(f6042,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f5817,f1745])).

fof(f1745,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f325,f1698])).

fof(f1698,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f1696])).

fof(f1696,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f857,f181])).

fof(f5817,plain,(
    k1_relat_1(sK3) = sK0 ),
    inference(subsumption_resolution,[],[f4920,f2790])).

fof(f2790,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) = sK0 ),
    inference(duplicate_literal_removal,[],[f2789])).

fof(f2789,plain,
    ( k1_relat_1(sK3) = sK0
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) = sK0 ),
    inference(forward_demodulation,[],[f2788,f100])).

fof(f2788,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) = sK0
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(superposition,[],[f311,f98])).

fof(f311,plain,
    ( v1_funct_2(sK3,sK1,sK1)
    | k1_relat_1(sK3) = sK0 ),
    inference(forward_demodulation,[],[f310,f100])).

fof(f310,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK1) ),
    inference(subsumption_resolution,[],[f309,f98])).

fof(f309,plain,
    ( k1_xboole_0 != sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK1) ),
    inference(subsumption_resolution,[],[f299,f61])).

fof(f299,plain,
    ( k1_xboole_0 != sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f129,f60])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X1,X0)
      | k1_xboole_0 != sK1
      | k1_relset_1(X1,X0,X2) = X1
      | v1_funct_2(sK3,X0,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(superposition,[],[f122,f84])).

fof(f4920,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) = sK0 ),
    inference(backward_demodulation,[],[f4874,f440])).

fof(f440,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f439,f100])).

fof(f439,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(trivial_inequality_removal,[],[f438])).

fof(f438,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(superposition,[],[f246,f98])).

fof(f9729,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f9301,f9517])).

fof(f9517,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f8491])).

fof(f8491,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    inference(backward_demodulation,[],[f8197,f3940])).

fof(f3940,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f3926,f802])).

fof(f802,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(superposition,[],[f61,f401])).

fof(f3926,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(resolution,[],[f801,f96])).

fof(f96,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f801,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(superposition,[],[f60,f401])).

fof(f9301,plain,(
    k1_relset_1(k1_xboole_0,sK1,sK3) = sK0 ),
    inference(trivial_inequality_removal,[],[f8730])).

fof(f8730,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,sK3) = sK0 ),
    inference(backward_demodulation,[],[f8197,f5953])).

fof(f5953,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = sK0
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f5817,f803])).

fof(f803,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3)
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(superposition,[],[f100,f401])).
%------------------------------------------------------------------------------
