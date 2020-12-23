%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 (3455 expanded)
%              Number of leaves         :   10 (1085 expanded)
%              Depth                    :   32
%              Number of atoms          :  780 (55828 expanded)
%              Number of equality atoms :  357 (24608 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(global_subsumption,[],[f229,f242,f252])).

fof(f252,plain,(
    r2_hidden(sK5(sK2,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f100,f30,f41,f105,f242,f116])).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),sK0)
      | k1_relat_1(X0) != sK1
      | r2_hidden(sK4(sK2,X0),sK1)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f115,f93])).

fof(f93,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f86,f84])).

fof(f84,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f40,f28,f29,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X4,X5] :
        ( ( ( k1_funct_1(sK3,X4) = X5
            & r2_hidden(X4,sK1) )
          | k1_funct_1(sK2,X5) != X4
          | ~ r2_hidden(X5,sK0) )
        & ( ( k1_funct_1(sK2,X5) = X4
            & r2_hidden(X5,sK0) )
          | k1_funct_1(sK3,X4) != X5
          | ~ r2_hidden(X4,sK1) ) )
    & v2_funct_1(sK2)
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & ! [X4,X5] :
                ( ( ( k1_funct_1(X3,X4) = X5
                    & r2_hidden(X4,X1) )
                  | k1_funct_1(X2,X5) != X4
                  | ~ r2_hidden(X5,X0) )
                & ( ( k1_funct_1(X2,X5) = X4
                    & r2_hidden(X5,X0) )
                  | k1_funct_1(X3,X4) != X5
                  | ~ r2_hidden(X4,X1) ) )
            & v2_funct_1(X2)
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & ! [X5,X4] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,sK1) )
                | k1_funct_1(sK2,X5) != X4
                | ~ r2_hidden(X5,sK0) )
              & ( ( k1_funct_1(sK2,X5) = X4
                  & r2_hidden(X5,sK0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,sK1) ) )
          & v2_funct_1(sK2)
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & ! [X5,X4] :
            ( ( ( k1_funct_1(X3,X4) = X5
                & r2_hidden(X4,sK1) )
              | k1_funct_1(sK2,X5) != X4
              | ~ r2_hidden(X5,sK0) )
            & ( ( k1_funct_1(sK2,X5) = X4
                & r2_hidden(X5,sK0) )
              | k1_funct_1(X3,X4) != X5
              | ~ r2_hidden(X4,sK1) ) )
        & v2_funct_1(sK2)
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5,X4] :
          ( ( ( k1_funct_1(sK3,X4) = X5
              & r2_hidden(X4,sK1) )
            | k1_funct_1(sK2,X5) != X4
            | ~ r2_hidden(X5,sK0) )
          & ( ( k1_funct_1(sK2,X5) = X4
              & r2_hidden(X5,sK0) )
            | k1_funct_1(sK3,X4) != X5
            | ~ r2_hidden(X4,sK1) ) )
      & v2_funct_1(sK2)
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) )
                     => ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) ) )
                    & ( ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) )
                     => ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) ) ) )
                & v2_funct_1(X2)
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) )
                   => ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) ) )
                  & ( ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) )
                   => ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) ) ) )
              & v2_funct_1(X2)
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).

fof(f28,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f29,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f115,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK4(sK2,X0),sK1)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f114,f87])).

fof(f87,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f57,f29,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f114,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK4(sK2,X0),sK1)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f113,f27])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f113,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK4(sK2,X0),sK1)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f108,f34])).

fof(f34,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK4(sK2,X0),sK1)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f48,f92])).

fof(f92,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f85,f33])).

fof(f33,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f29,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_relat_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( sK5(X0,X1) != k1_funct_1(X1,sK4(X0,X1))
                  | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0)) )
                & sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
              | ( ( sK4(X0,X1) != k1_funct_1(X0,sK5(X0,X1))
                  | ~ r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                & sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1))
                & r2_hidden(sK4(X0,X1),k2_relat_1(X0)) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( sK5(X0,X1) != k1_funct_1(X1,sK4(X0,X1))
            | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0)) )
          & sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
          & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
        | ( ( sK4(X0,X1) != k1_funct_1(X0,sK5(X0,X1))
            | ~ r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
          & sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1))
          & r2_hidden(sK4(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f105,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f99,f97])).

fof(f97,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(unit_resulting_resolution,[],[f39,f31,f32,f60])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f99,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK0,sK3) ),
    inference(unit_resulting_resolution,[],[f32,f58])).

fof(f41,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f57,f32,f42])).

fof(f242,plain,(
    ~ r2_hidden(sK4(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f241,f100])).

fof(f241,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f240,f30])).

fof(f240,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f239,f41])).

fof(f239,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f238,f219])).

fof(f219,plain,(
    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(superposition,[],[f216,f160])).

fof(f160,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f159,f100])).

fof(f159,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f158,f30])).

fof(f158,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f155,f41])).

fof(f155,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,
    ( sK1 != sK1
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f126,f105])).

fof(f126,plain,(
    ! [X3] :
      ( sK1 != k1_relat_1(X3)
      | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3))
      | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
      | k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f125,f87])).

fof(f125,plain,(
    ! [X3] :
      ( sK1 != k1_relat_1(X3)
      | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3))
      | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
      | k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f124,f27])).

fof(f124,plain,(
    ! [X3] :
      ( sK1 != k1_relat_1(X3)
      | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3))
      | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
      | k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f111,f34])).

fof(f111,plain,(
    ! [X3] :
      ( sK1 != k1_relat_1(X3)
      | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3))
      | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
      | k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f52,f92])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_relat_1(X0)
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1))
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f216,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3)))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f215,f100])).

fof(f215,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f214,f30])).

fof(f214,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f211,f41])).

fof(f211,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3))) ),
    inference(trivial_inequality_removal,[],[f210])).

fof(f210,plain,
    ( sK1 != sK1
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3))) ),
    inference(superposition,[],[f152,f105])).

fof(f152,plain,(
    ! [X3] :
      ( sK1 != k1_relat_1(X3)
      | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3))
      | k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | sK4(sK2,X3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,X3))) ) ),
    inference(resolution,[],[f123,f68])).

fof(f68,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK2,k1_funct_1(sK3,X4)) = X4 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK2,X5) = X4
      | k1_funct_1(sK3,X4) != X5
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f123,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK2,X2),sK1)
      | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2))
      | k1_relat_1(X2) != sK1
      | k2_funct_1(sK2) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f122,f87])).

fof(f122,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2))
      | r2_hidden(sK4(sK2,X2),sK1)
      | k2_funct_1(sK2) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f121,f27])).

fof(f121,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2))
      | r2_hidden(sK4(sK2,X2),sK1)
      | k2_funct_1(sK2) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f110,f34])).

fof(f110,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2))
      | r2_hidden(sK4(sK2,X2),sK1)
      | k2_funct_1(sK2) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f51,f92])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_relat_1(X0)
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f238,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f237,f222])).

fof(f222,plain,(
    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    inference(backward_demodulation,[],[f206,f219])).

fof(f206,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3)))
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f205,f100])).

fof(f205,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f204,f30])).

fof(f204,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f201,f41])).

fof(f201,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3))) ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,
    ( sK1 != sK1
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3))) ),
    inference(superposition,[],[f145,f105])).

fof(f145,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | sK5(sK2,X2) = k1_funct_1(X2,sK4(sK2,X2))
      | k2_funct_1(sK2) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sK5(sK2,X2) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,X2))) ) ),
    inference(resolution,[],[f120,f66])).

fof(f66,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK3,k1_funct_1(sK2,X5)) = X5 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK3,X4) = X5
      | k1_funct_1(sK2,X5) != X4
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f120,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,X1),sK0)
      | k1_relat_1(X1) != sK1
      | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f119,f93])).

fof(f119,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK1
      | r2_hidden(sK5(sK2,X1),k1_relat_1(sK2))
      | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f118,f87])).

fof(f118,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK1
      | r2_hidden(sK5(sK2,X1),k1_relat_1(sK2))
      | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f117,f27])).

fof(f117,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK1
      | r2_hidden(sK5(sK2,X1),k1_relat_1(sK2))
      | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f109,f34])).

fof(f109,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK1
      | r2_hidden(sK5(sK2,X1),k1_relat_1(sK2))
      | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f49,f92])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_relat_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1))
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f237,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f236,f105])).

fof(f236,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | sK1 != k1_relat_1(sK3)
    | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | sK1 != k1_relat_1(sK3)
    | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f223,f130])).

fof(f130,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK5(sK2,X4),sK0)
      | sK1 != k1_relat_1(X4)
      | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4))
      | ~ r2_hidden(sK4(sK2,X4),sK1)
      | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4))
      | k2_funct_1(sK2) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(forward_demodulation,[],[f129,f93])).

fof(f129,plain,(
    ! [X4] :
      ( sK1 != k1_relat_1(X4)
      | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4))
      | ~ r2_hidden(sK4(sK2,X4),sK1)
      | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4))
      | ~ r2_hidden(sK5(sK2,X4),k1_relat_1(sK2))
      | k2_funct_1(sK2) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f128,f87])).

fof(f128,plain,(
    ! [X4] :
      ( sK1 != k1_relat_1(X4)
      | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4))
      | ~ r2_hidden(sK4(sK2,X4),sK1)
      | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4))
      | ~ r2_hidden(sK5(sK2,X4),k1_relat_1(sK2))
      | k2_funct_1(sK2) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f127,f27])).

fof(f127,plain,(
    ! [X4] :
      ( sK1 != k1_relat_1(X4)
      | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4))
      | ~ r2_hidden(sK4(sK2,X4),sK1)
      | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4))
      | ~ r2_hidden(sK5(sK2,X4),k1_relat_1(sK2))
      | k2_funct_1(sK2) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f112,f34])).

fof(f112,plain,(
    ! [X4] :
      ( sK1 != k1_relat_1(X4)
      | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4))
      | ~ r2_hidden(sK4(sK2,X4),sK1)
      | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4))
      | ~ r2_hidden(sK5(sK2,X4),k1_relat_1(sK2))
      | k2_funct_1(sK2) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f56,f92])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_relat_1(X0)
      | sK5(X0,X1) != k1_funct_1(X1,sK4(X0,X1))
      | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | sK4(X0,X1) != k1_funct_1(X0,sK5(X0,X1))
      | ~ r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f223,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),sK1) ),
    inference(superposition,[],[f69,f222])).

fof(f69,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK3,X4),sK0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK0)
      | k1_funct_1(sK3,X4) != X5
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f229,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | ~ r2_hidden(sK5(sK2,sK3),sK0) ),
    inference(superposition,[],[f67,f219])).

fof(f67,plain,(
    ! [X5] :
      ( r2_hidden(k1_funct_1(sK2,X5),sK1)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,sK1)
      | k1_funct_1(sK2,X5) != X4
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f20])).

% (27232)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (27244)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.45  % (27235)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (27244)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f257,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(global_subsumption,[],[f229,f242,f252])).
% 0.21/0.46  fof(f252,plain,(
% 0.21/0.46    r2_hidden(sK5(sK2,sK3),sK0)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f100,f30,f41,f105,f242,f116])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK5(sK2,X0),sK0) | k1_relat_1(X0) != sK1 | r2_hidden(sK4(sK2,X0),sK1) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f115,f93])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK2)),
% 0.21/0.46    inference(backward_demodulation,[],[f86,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f40,f28,f29,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(nnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X4,X5] : (((k1_funct_1(sK3,X4) = X5 & r2_hidden(X4,sK1)) | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) & ((k1_funct_1(sK2,X5) = X4 & r2_hidden(X5,sK0)) | k1_funct_1(sK3,X4) != X5 | ~r2_hidden(X4,sK1))) & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f19,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK1)) | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) & ((k1_funct_1(sK2,X5) = X4 & r2_hidden(X5,sK0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK1))) & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK1)) | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) & ((k1_funct_1(sK2,X5) = X4 & r2_hidden(X5,sK0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK1))) & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5,X4] : (((k1_funct_1(sK3,X4) = X5 & r2_hidden(X4,sK1)) | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) & ((k1_funct_1(sK2,X5) = X4 & r2_hidden(X5,sK0)) | k1_funct_1(sK3,X4) != X5 | ~r2_hidden(X4,sK1))) & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | (k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0))) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | (k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    k1_xboole_0 != sK1),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f29,f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),sK1) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f114,f87])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f57,f29,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),sK1) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f113,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    v1_funct_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),sK1) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f108,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    v2_funct_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),sK1) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.46    inference(superposition,[],[f48,f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    sK1 = k2_relat_1(sK2)),
% 0.21/0.46    inference(forward_demodulation,[],[f85,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f29,f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_relat_1(X1) != k2_relat_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r2_hidden(sK4(X0,X1),k2_relat_1(X0)) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((sK5(X0,X1) != k1_funct_1(X1,sK4(X0,X1)) | ~r2_hidden(sK4(X0,X1),k2_relat_1(X0))) & sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | ((sK4(X0,X1) != k1_funct_1(X0,sK5(X0,X1)) | ~r2_hidden(sK5(X0,X1),k1_relat_1(X0))) & sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) => (((sK5(X0,X1) != k1_funct_1(X1,sK4(X0,X1)) | ~r2_hidden(sK4(X0,X1),k2_relat_1(X0))) & sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | ((sK4(X0,X1) != k1_funct_1(X0,sK5(X0,X1)) | ~r2_hidden(sK5(X0,X1),k1_relat_1(X0))) & sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k2_relat_1(X0)))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(rectify,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    sK1 = k1_relat_1(sK3)),
% 0.21/0.46    inference(backward_demodulation,[],[f99,f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f39,f31,f32,f60])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    k1_xboole_0 != sK0),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    k1_relat_1(sK3) = k1_relset_1(sK1,sK0,sK3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f32,f58])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    k2_funct_1(sK2) != sK3),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    v1_funct_1(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    v1_relat_1(sK3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f57,f32,f42])).
% 0.21/0.46  fof(f242,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK2,sK3),sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f241,f100])).
% 0.21/0.46  fof(f241,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK2,sK3),sK1) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f240,f30])).
% 0.21/0.46  fof(f240,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK2,sK3),sK1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f239,f41])).
% 0.21/0.46  fof(f239,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK2,sK3),sK1) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f238,f219])).
% 0.21/0.46  fof(f219,plain,(
% 0.21/0.46    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f217])).
% 0.21/0.46  fof(f217,plain,(
% 0.21/0.46    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))),
% 0.21/0.46    inference(superposition,[],[f216,f160])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))),
% 0.21/0.46    inference(subsumption_resolution,[],[f159,f100])).
% 0.21/0.46  fof(f159,plain,(
% 0.21/0.46    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f158,f30])).
% 0.21/0.46  fof(f158,plain,(
% 0.21/0.46    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f155,f41])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f154])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    sK1 != sK1 | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(superposition,[],[f126,f105])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ( ! [X3] : (sK1 != k1_relat_1(X3) | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3)) | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3)) | k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f125,f87])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    ( ! [X3] : (sK1 != k1_relat_1(X3) | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3)) | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3)) | k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_relat_1(sK2)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f124,f27])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    ( ! [X3] : (sK1 != k1_relat_1(X3) | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3)) | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3)) | k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f111,f34])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    ( ! [X3] : (sK1 != k1_relat_1(X3) | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3)) | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3)) | k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.46    inference(superposition,[],[f52,f92])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_relat_1(X1) != k2_relat_1(X0) | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) | sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1)) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3))) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))),
% 0.21/0.46    inference(subsumption_resolution,[],[f215,f100])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | ~v1_relat_1(sK3) | sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3)))),
% 0.21/0.46    inference(subsumption_resolution,[],[f214,f30])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3)))),
% 0.21/0.46    inference(subsumption_resolution,[],[f211,f41])).
% 0.21/0.46  fof(f211,plain,(
% 0.21/0.46    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3)))),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f210])).
% 0.21/0.46  fof(f210,plain,(
% 0.21/0.46    sK1 != sK1 | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3)))),
% 0.21/0.46    inference(superposition,[],[f152,f105])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    ( ! [X3] : (sK1 != k1_relat_1(X3) | sK4(sK2,X3) = k1_funct_1(sK2,sK5(sK2,X3)) | k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | sK4(sK2,X3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,X3)))) )),
% 0.21/0.46    inference(resolution,[],[f123,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X4] : (~r2_hidden(X4,sK1) | k1_funct_1(sK2,k1_funct_1(sK3,X4)) = X4) )),
% 0.21/0.46    inference(equality_resolution,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X4,X5] : (k1_funct_1(sK2,X5) = X4 | k1_funct_1(sK3,X4) != X5 | ~r2_hidden(X4,sK1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    ( ! [X2] : (r2_hidden(sK4(sK2,X2),sK1) | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2)) | k1_relat_1(X2) != sK1 | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f122,f87])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    ( ! [X2] : (k1_relat_1(X2) != sK1 | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2)) | r2_hidden(sK4(sK2,X2),sK1) | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(sK2)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f121,f27])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X2] : (k1_relat_1(X2) != sK1 | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2)) | r2_hidden(sK4(sK2,X2),sK1) | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f110,f34])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X2] : (k1_relat_1(X2) != sK1 | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2)) | r2_hidden(sK4(sK2,X2),sK1) | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(superposition,[],[f51,f92])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_relat_1(X1) != k2_relat_1(X0) | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) | r2_hidden(sK4(X0,X1),k2_relat_1(X0)) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    ~r2_hidden(sK4(sK2,sK3),sK1) | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f237,f222])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f220])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 0.21/0.47    inference(backward_demodulation,[],[f206,f219])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3))) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 0.21/0.47    inference(subsumption_resolution,[],[f205,f100])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~v1_relat_1(sK3) | sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f204,f30])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f201,f41])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3)))),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f200])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    sK1 != sK1 | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3)))),
% 0.21/0.47    inference(superposition,[],[f145,f105])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ( ! [X2] : (k1_relat_1(X2) != sK1 | sK5(sK2,X2) = k1_funct_1(X2,sK4(sK2,X2)) | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | sK5(sK2,X2) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,X2)))) )),
% 0.21/0.47    inference(resolution,[],[f120,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X5] : (~r2_hidden(X5,sK0) | k1_funct_1(sK3,k1_funct_1(sK2,X5)) = X5) )),
% 0.21/0.47    inference(equality_resolution,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k1_funct_1(sK3,X4) = X5 | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X1] : (r2_hidden(sK5(sK2,X1),sK0) | k1_relat_1(X1) != sK1 | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1)) | k2_funct_1(sK2) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f119,f93])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X1] : (k1_relat_1(X1) != sK1 | r2_hidden(sK5(sK2,X1),k1_relat_1(sK2)) | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1)) | k2_funct_1(sK2) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f118,f87])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X1] : (k1_relat_1(X1) != sK1 | r2_hidden(sK5(sK2,X1),k1_relat_1(sK2)) | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1)) | k2_funct_1(sK2) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f117,f27])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X1] : (k1_relat_1(X1) != sK1 | r2_hidden(sK5(sK2,X1),k1_relat_1(sK2)) | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1)) | k2_funct_1(sK2) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f109,f34])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X1] : (k1_relat_1(X1) != sK1 | r2_hidden(sK5(sK2,X1),k1_relat_1(sK2)) | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1)) | k2_funct_1(sK2) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(superposition,[],[f49,f92])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_relat_1(X1) != k2_relat_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1)) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    ~r2_hidden(sK4(sK2,sK3),sK1) | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3)) | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f236,f105])).
% 0.21/0.47  fof(f236,plain,(
% 0.21/0.47    ~r2_hidden(sK4(sK2,sK3),sK1) | sK1 != k1_relat_1(sK3) | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3)) | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f230])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    ~r2_hidden(sK4(sK2,sK3),sK1) | sK1 != k1_relat_1(sK3) | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3)) | ~r2_hidden(sK4(sK2,sK3),sK1) | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.47    inference(resolution,[],[f223,f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ( ! [X4] : (~r2_hidden(sK5(sK2,X4),sK0) | sK1 != k1_relat_1(X4) | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4)) | ~r2_hidden(sK4(sK2,X4),sK1) | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4)) | k2_funct_1(sK2) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f129,f93])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ( ! [X4] : (sK1 != k1_relat_1(X4) | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4)) | ~r2_hidden(sK4(sK2,X4),sK1) | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4)) | ~r2_hidden(sK5(sK2,X4),k1_relat_1(sK2)) | k2_funct_1(sK2) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f128,f87])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X4] : (sK1 != k1_relat_1(X4) | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4)) | ~r2_hidden(sK4(sK2,X4),sK1) | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4)) | ~r2_hidden(sK5(sK2,X4),k1_relat_1(sK2)) | k2_funct_1(sK2) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f127,f27])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ( ! [X4] : (sK1 != k1_relat_1(X4) | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4)) | ~r2_hidden(sK4(sK2,X4),sK1) | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4)) | ~r2_hidden(sK5(sK2,X4),k1_relat_1(sK2)) | k2_funct_1(sK2) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f112,f34])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ( ! [X4] : (sK1 != k1_relat_1(X4) | sK5(sK2,X4) != k1_funct_1(X4,sK4(sK2,X4)) | ~r2_hidden(sK4(sK2,X4),sK1) | sK4(sK2,X4) != k1_funct_1(sK2,sK5(sK2,X4)) | ~r2_hidden(sK5(sK2,X4),k1_relat_1(sK2)) | k2_funct_1(sK2) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(superposition,[],[f56,f92])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_relat_1(X1) != k2_relat_1(X0) | sK5(X0,X1) != k1_funct_1(X1,sK4(X0,X1)) | ~r2_hidden(sK4(X0,X1),k2_relat_1(X0)) | sK4(X0,X1) != k1_funct_1(X0,sK5(X0,X1)) | ~r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    r2_hidden(sK5(sK2,sK3),sK0) | ~r2_hidden(sK4(sK2,sK3),sK1)),
% 0.21/0.47    inference(superposition,[],[f69,f222])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X4] : (r2_hidden(k1_funct_1(sK3,X4),sK0) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X4,X5] : (r2_hidden(X5,sK0) | k1_funct_1(sK3,X4) != X5 | ~r2_hidden(X4,sK1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    r2_hidden(sK4(sK2,sK3),sK1) | ~r2_hidden(sK5(sK2,sK3),sK0)),
% 0.21/0.47    inference(superposition,[],[f67,f219])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X5] : (r2_hidden(k1_funct_1(sK2,X5),sK1) | ~r2_hidden(X5,sK0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X4,X5] : (r2_hidden(X4,sK1) | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  % (27232)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (27244)------------------------------
% 0.21/0.47  % (27244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27244)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (27244)Memory used [KB]: 6524
% 0.21/0.47  % (27244)Time elapsed: 0.024 s
% 0.21/0.47  % (27244)------------------------------
% 0.21/0.47  % (27244)------------------------------
% 0.21/0.47  % (27223)Success in time 0.115 s
%------------------------------------------------------------------------------
