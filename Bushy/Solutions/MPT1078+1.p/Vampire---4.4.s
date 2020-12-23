%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t195_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:40 EDT 2019

% Result     : Theorem 4.01s
% Output     : Refutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  107 (1698 expanded)
%              Number of leaves         :   18 ( 747 expanded)
%              Depth                    :   16
%              Number of atoms          :  428 (16915 expanded)
%              Number of equality atoms :   20 ( 121 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19670,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19669,f2654])).

fof(f2654,plain,(
    r1_tarski(k2_relat_1(sK5),k1_relat_1(k7_relat_1(sK6,sK4))) ),
    inference(unit_resulting_resolution,[],[f454,f576,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t1_xboole_1)).

fof(f576,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK6,sK3)),k1_relat_1(k7_relat_1(sK6,sK4))) ),
    inference(unit_resulting_resolution,[],[f194,f194,f192,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t25_relat_1)).

fof(f192,plain,(
    r1_tarski(k7_relat_1(sK6,sK3),k7_relat_1(sK6,sK4)) ),
    inference(unit_resulting_resolution,[],[f102,f163,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t104_relat_1)).

fof(f163,plain,(
    v1_relat_1(sK6) ),
    inference(unit_resulting_resolution,[],[f100,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',cc1_relset_1)).

fof(f100,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,
    ( ~ r2_funct_2(sK0,sK2,k8_funct_2(sK0,sK1,sK2,sK5,k2_partfun1(sK1,sK2,sK6,sK3)),k8_funct_2(sK0,sK1,sK2,sK5,k2_partfun1(sK1,sK2,sK6,sK4)))
    & r1_tarski(sK3,sK4)
    & r1_tarski(k2_relset_1(sK0,sK1,sK5),k1_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK6,sK3)))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK5,sK0,sK1)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f85,f84,f83,f82])).

fof(f82,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3,X4,X5] :
                ( ? [X6] :
                    ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                    & r1_tarski(X3,X4)
                    & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X5,X0,X1)
                & v1_funct_1(X5) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X5,X4,X3,X2] :
              ( ? [X6] :
                  ( ~ r2_funct_2(sK0,X2,k8_funct_2(sK0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(sK0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                  & r1_tarski(X3,X4)
                  & r1_tarski(k2_relset_1(sK0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X5,sK0,X1)
              & v1_funct_1(X5) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3,X4,X5] :
              ( ? [X6] :
                  ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                  & r1_tarski(X3,X4)
                  & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X5,X0,X1)
              & v1_funct_1(X5) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X5,X4,X3,X2] :
            ( ? [X6] :
                ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,sK1,X2,X5,k2_partfun1(sK1,X2,X6,X3)),k8_funct_2(X0,sK1,X2,X5,k2_partfun1(sK1,X2,X6,X4)))
                & r1_tarski(X3,X4)
                & r1_tarski(k2_relset_1(X0,sK1,X5),k1_relset_1(sK1,X2,k2_partfun1(sK1,X2,X6,X3)))
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
            & v1_funct_2(X5,X0,sK1)
            & v1_funct_1(X5) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ? [X2,X3,X4,X5] :
          ( ? [X6] :
              ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
              & r1_tarski(X3,X4)
              & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X5,X0,X1)
          & v1_funct_1(X5) )
     => ( ? [X6] :
            ( ~ r2_funct_2(X0,sK2,k8_funct_2(X0,X1,sK2,sK5,k2_partfun1(X1,sK2,X6,sK3)),k8_funct_2(X0,X1,sK2,sK5,k2_partfun1(X1,sK2,X6,sK4)))
            & r1_tarski(sK3,sK4)
            & r1_tarski(k2_relset_1(X0,X1,sK5),k1_relset_1(X1,sK2,k2_partfun1(X1,sK2,X6,sK3)))
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
            & v1_funct_1(X6) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
          & r1_tarski(X3,X4)
          & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,sK6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,sK6,X4)))
        & r1_tarski(X3,X4)
        & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,sK6,X3)))
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3,X4,X5] :
              ( ? [X6] :
                  ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                  & r1_tarski(X3,X4)
                  & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X5,X0,X1)
              & v1_funct_1(X5) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3,X4,X5] :
              ( ? [X6] :
                  ( ~ r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4)))
                  & r1_tarski(X3,X4)
                  & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3)))
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X5,X0,X1)
              & v1_funct_1(X5) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3,X4,X5] :
                ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X5,X0,X1)
                  & v1_funct_1(X5) )
               => ! [X6] :
                    ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_1(X6) )
                   => ( ( r1_tarski(X3,X4)
                        & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3))) )
                     => r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3,X4,X5] :
              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X5,X0,X1)
                & v1_funct_1(X5) )
             => ! [X6] :
                  ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_1(X6) )
                 => ( ( r1_tarski(X3,X4)
                      & r1_tarski(k2_relset_1(X0,X1,X5),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X6,X3))) )
                   => r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X3)),k8_funct_2(X0,X1,X2,X5,k2_partfun1(X1,X2,X6,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t195_funct_2)).

fof(f102,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f86])).

fof(f194,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK6,X0)) ),
    inference(unit_resulting_resolution,[],[f163,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',dt_k7_relat_1)).

fof(f454,plain,(
    r1_tarski(k2_relat_1(sK5),k1_relat_1(k7_relat_1(sK6,sK3))) ),
    inference(subsumption_resolution,[],[f363,f379])).

fof(f379,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK6,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(forward_demodulation,[],[f204,f198])).

fof(f198,plain,(
    ! [X0] : k2_partfun1(sK1,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(unit_resulting_resolution,[],[f99,f100,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',redefinition_k2_partfun1)).

fof(f99,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f86])).

fof(f204,plain,(
    ! [X0] : m1_subset_1(k2_partfun1(sK1,sK2,sK6,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f137])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',dt_k2_partfun1)).

fof(f363,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relat_1(k7_relat_1(sK6,sK3)))
    | ~ m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(superposition,[],[f344,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',redefinition_k1_relset_1)).

fof(f344,plain,(
    r1_tarski(k2_relat_1(sK5),k1_relset_1(sK1,sK2,k7_relat_1(sK6,sK3))) ),
    inference(backward_demodulation,[],[f198,f292])).

fof(f292,plain,(
    r1_tarski(k2_relat_1(sK5),k1_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK6,sK3))) ),
    inference(backward_demodulation,[],[f177,f101])).

fof(f101,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK5),k1_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK6,sK3))) ),
    inference(cnf_transformation,[],[f86])).

fof(f177,plain,(
    k2_relset_1(sK0,sK1,sK5) = k2_relat_1(sK5) ),
    inference(unit_resulting_resolution,[],[f98,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',redefinition_k2_relset_1)).

fof(f98,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f86])).

fof(f19669,plain,(
    ~ r1_tarski(k2_relat_1(sK5),k1_relat_1(k7_relat_1(sK6,sK4))) ),
    inference(forward_demodulation,[],[f19668,f177])).

fof(f19668,plain,(
    ~ r1_tarski(k2_relset_1(sK0,sK1,sK5),k1_relat_1(k7_relat_1(sK6,sK4))) ),
    inference(forward_demodulation,[],[f19667,f381])).

fof(f381,plain,(
    ! [X0] : k1_relset_1(sK1,sK2,k7_relat_1(sK6,X0)) = k1_relat_1(k7_relat_1(sK6,X0)) ),
    inference(unit_resulting_resolution,[],[f379,f121])).

fof(f19667,plain,(
    ~ r1_tarski(k2_relset_1(sK0,sK1,sK5),k1_relset_1(sK1,sK2,k7_relat_1(sK6,sK4))) ),
    inference(forward_demodulation,[],[f19665,f198])).

fof(f19665,plain,(
    ~ r1_tarski(k2_relset_1(sK0,sK1,sK5),k1_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK6,sK4))) ),
    inference(unit_resulting_resolution,[],[f94,f95,f96,f99,f97,f98,f100,f17287,f223])).

fof(f223,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(X4,X1,k8_funct_2(X4,X0,X1,X5,k7_relat_1(X2,X3)),k8_funct_2(X4,X0,X1,X5,X2))
      | ~ r1_tarski(k2_relset_1(X4,X0,X5),k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))
      | ~ v1_funct_2(X5,X4,X0)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(X4,X1,k8_funct_2(X4,X0,X1,X5,k7_relat_1(X2,X3)),k8_funct_2(X4,X0,X1,X5,X2))
      | ~ r1_tarski(k2_relset_1(X4,X0,X5),k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))
      | ~ v1_funct_2(X5,X4,X0)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f106,f135])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X4,k2_partfun1(X1,X2,X5,X3)),k8_funct_2(X0,X1,X2,X4,X5))
      | ~ r1_tarski(k2_relset_1(X0,X1,X4),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X5,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3,X4] :
              ( ! [X5] :
                  ( r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X4,k2_partfun1(X1,X2,X5,X3)),k8_funct_2(X0,X1,X2,X4,X5))
                  | ~ r1_tarski(k2_relset_1(X0,X1,X4),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X5,X3)))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3,X4] :
              ( ! [X5] :
                  ( r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X4,k2_partfun1(X1,X2,X5,X3)),k8_funct_2(X0,X1,X2,X4,X5))
                  | ~ r1_tarski(k2_relset_1(X0,X1,X4),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X5,X3)))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3,X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_1(X5) )
                 => ( r1_tarski(k2_relset_1(X0,X1,X4),k1_relset_1(X1,X2,k2_partfun1(X1,X2,X5,X3)))
                   => r2_funct_2(X0,X2,k8_funct_2(X0,X1,X2,X4,k2_partfun1(X1,X2,X5,X3)),k8_funct_2(X0,X1,X2,X4,X5)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t194_funct_2)).

fof(f17287,plain,(
    ~ r2_funct_2(sK0,sK2,k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,sK4)),k8_funct_2(sK0,sK1,sK2,sK5,sK6)) ),
    inference(unit_resulting_resolution,[],[f213,f389,f219,f390,f220,f391,f17245,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | r2_funct_2(X0,X1,X3,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X3,X2)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X3,X2)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
       => r2_funct_2(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',symmetry_r2_funct_2)).

fof(f17245,plain,(
    ~ r2_funct_2(sK0,sK2,k8_funct_2(sK0,sK1,sK2,sK5,sK6),k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,sK4))) ),
    inference(backward_demodulation,[],[f1323,f349])).

fof(f349,plain,(
    ~ r2_funct_2(sK0,sK2,k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,sK3)),k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,sK4))) ),
    inference(forward_demodulation,[],[f345,f198])).

fof(f345,plain,(
    ~ r2_funct_2(sK0,sK2,k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,sK3)),k8_funct_2(sK0,sK1,sK2,sK5,k2_partfun1(sK1,sK2,sK6,sK4))) ),
    inference(backward_demodulation,[],[f198,f103])).

fof(f103,plain,(
    ~ r2_funct_2(sK0,sK2,k8_funct_2(sK0,sK1,sK2,sK5,k2_partfun1(sK1,sK2,sK6,sK3)),k8_funct_2(sK0,sK1,sK2,sK5,k2_partfun1(sK1,sK2,sK6,sK4))) ),
    inference(cnf_transformation,[],[f86])).

fof(f1323,plain,(
    k8_funct_2(sK0,sK1,sK2,sK5,sK6) = k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,sK3)) ),
    inference(unit_resulting_resolution,[],[f213,f389,f219,f390,f220,f493,f391,f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',redefinition_r2_funct_2)).

fof(f493,plain,(
    r2_funct_2(sK0,sK2,k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,sK3)),k8_funct_2(sK0,sK1,sK2,sK5,sK6)) ),
    inference(forward_demodulation,[],[f221,f198])).

fof(f221,plain,(
    r2_funct_2(sK0,sK2,k8_funct_2(sK0,sK1,sK2,sK5,k2_partfun1(sK1,sK2,sK6,sK3)),k8_funct_2(sK0,sK1,sK2,sK5,sK6)) ),
    inference(unit_resulting_resolution,[],[f94,f95,f96,f99,f97,f98,f100,f101,f106])).

fof(f391,plain,(
    ! [X0] : m1_subset_1(k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,X0)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f96,f346,f97,f98,f379,f140])).

fof(f140,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',dt_k8_funct_2)).

fof(f346,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK6,X0)) ),
    inference(backward_demodulation,[],[f198,f196])).

fof(f196,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK1,sK2,sK6,X0)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f136])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f220,plain,(
    m1_subset_1(k8_funct_2(sK0,sK1,sK2,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f96,f99,f97,f98,f100,f140])).

fof(f390,plain,(
    ! [X0] : v1_funct_2(k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,X0)),sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f96,f346,f97,f98,f379,f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f219,plain,(
    v1_funct_2(k8_funct_2(sK0,sK1,sK2,sK5,sK6),sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f96,f99,f97,f98,f100,f139])).

fof(f389,plain,(
    ! [X0] : v1_funct_1(k8_funct_2(sK0,sK1,sK2,sK5,k7_relat_1(sK6,X0))) ),
    inference(unit_resulting_resolution,[],[f96,f346,f97,f98,f379,f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f213,plain,(
    v1_funct_1(k8_funct_2(sK0,sK1,sK2,sK5,sK6)) ),
    inference(unit_resulting_resolution,[],[f96,f99,f97,f98,f100,f138])).

fof(f97,plain,(
    v1_funct_2(sK5,sK0,sK1) ),
    inference(cnf_transformation,[],[f86])).

fof(f96,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f86])).

fof(f95,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

fof(f94,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f86])).
%------------------------------------------------------------------------------
