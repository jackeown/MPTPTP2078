%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t168_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:35 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 183 expanded)
%              Number of leaves         :    8 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 (1182 expanded)
%              Number of equality atoms :   37 ( 327 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(subsumption_resolution,[],[f157,f107])).

fof(f107,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f62,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t168_funct_2.p',reflexivity_r2_relset_1)).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3)
    & ! [X4] : k1_tarski(X4) != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f50,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
            & ! [X4] : k1_tarski(X4) != X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,X3)
          & ! [X4] : k1_tarski(X4) != sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK3)
        & k5_partfun1(X0,X1,sK3) = k5_partfun1(X0,X1,X2)
        & ! [X4] : k1_tarski(X4) != X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
                & ! [X4] : k1_tarski(X4) != X1 )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
              & ! [X4] : k1_tarski(X4) != X1 )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t168_funct_2.p',t168_funct_2)).

fof(f157,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(backward_demodulation,[],[f151,f67])).

fof(f67,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f151,plain,(
    sK2 = sK3 ),
    inference(unit_resulting_resolution,[],[f140,f149,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t168_funct_2.p',d10_xboole_0)).

fof(f149,plain,(
    r1_tarski(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f64,f141,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_relset_1(X0,X1,X2,X3)
      | r1_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_relset_1(X0,X1,X2,X3)
          | ~ r1_tarski(X2,X3) )
        & ( r1_tarski(X2,X3)
          | ~ r1_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t168_funct_2.p',redefinition_r1_relset_1)).

fof(f141,plain,(
    r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f61,f62,f90,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
      | r1_relset_1(sK0,sK1,sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f135,f63])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
      | r1_relset_1(sK0,sK1,sK3,X0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f134,f64])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
      | r1_relset_1(sK0,sK1,sK3,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f130,f65])).

fof(f65,plain,(
    ! [X4] : k1_tarski(X4) != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
      | k1_tarski(sK4(sK1)) = sK1
      | r1_relset_1(sK0,sK1,sK3,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(superposition,[],[f72,f66])).

fof(f66,plain,(
    k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
      | k1_tarski(sK4(X1)) = X1
      | r1_relset_1(X0,X1,X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | k1_tarski(sK4(X1)) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f53])).

fof(f53,plain,(
    ! [X1] :
      ( ? [X4] : k1_tarski(X4) = X1
     => k1_tarski(sK4(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( ! [X4] : k1_tarski(X4) != X1
              & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) )
           => r1_relset_1(X0,X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t168_funct_2.p',t167_funct_2)).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f140,plain,(
    r1_tarski(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f62,f138,f75])).

fof(f138,plain,(
    r1_relset_1(sK0,sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f61,f62,f90,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
      | r1_relset_1(sK0,sK1,X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f132,f63])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
      | r1_relset_1(sK0,sK1,X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f131,f64])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
      | r1_relset_1(sK0,sK1,X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f129,f65])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
      | k1_tarski(sK4(sK1)) = sK1
      | r1_relset_1(sK0,sK1,X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f72,f66])).
%------------------------------------------------------------------------------
