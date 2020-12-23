%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0988+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 (1761 expanded)
%              Number of leaves         :    6 ( 319 expanded)
%              Depth                    :   36
%              Number of atoms          :  600 (19609 expanded)
%              Number of equality atoms :  250 (8384 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f885,plain,(
    $false ),
    inference(resolution,[],[f884,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f884,plain,(
    ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(resolution,[],[f866,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f866,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f865,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f865,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f861,f42])).

fof(f861,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f860,f28])).

fof(f28,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f860,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f859,f803])).

fof(f803,plain,(
    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f759])).

fof(f759,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    inference(backward_demodulation,[],[f465,f672])).

fof(f672,plain,(
    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f654])).

fof(f654,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(superposition,[],[f385,f643])).

fof(f643,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(resolution,[],[f642,f31])).

fof(f642,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
      | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ) ),
    inference(resolution,[],[f378,f23])).

fof(f378,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
      | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f215,f42])).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
      | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f205,f42])).

fof(f205,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f204,f28])).

fof(f204,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f201,f127])).

fof(f127,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f125,f113])).

fof(f113,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f112,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f112,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f111,f23])).

fof(f111,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f22,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f22,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f125,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f23,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f201,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK1 != k1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(resolution,[],[f148,f21])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f148,plain,(
    ! [X2] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X2)
      | k1_relat_1(X2) != sK1
      | sK5(sK2,X2) = k1_funct_1(X2,sK4(sK2,X2))
      | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2))
      | k2_funct_1(sK2) = X2 ) ),
    inference(backward_demodulation,[],[f94,f146])).

fof(f146,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f143,f24])).

fof(f24,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f143,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f94,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != k2_relat_1(sK2)
      | sK5(sK2,X2) = k1_funct_1(X2,sK4(sK2,X2))
      | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2))
      | k2_funct_1(sK2) = X2 ) ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != k2_relat_1(sK2)
      | sK5(sK2,X2) = k1_funct_1(X2,sK4(sK2,X2))
      | sK4(sK2,X2) = k1_funct_1(sK2,sK5(sK2,X2))
      | k2_funct_1(sK2) = X2 ) ),
    inference(resolution,[],[f25,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1))
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f25,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f385,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3)))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(resolution,[],[f380,f51])).

fof(f51,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK2,k1_funct_1(sK3,X4)) = X4 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) != X5
      | k1_funct_1(sK2,X5) = X4 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f380,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(resolution,[],[f379,f31])).

fof(f379,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(sK2,sK3),sK1)
      | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ) ),
    inference(resolution,[],[f309,f23])).

fof(f309,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
      | r2_hidden(sK4(sK2,sK3),sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f308,f42])).

fof(f308,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(sK4(sK2,sK3),sK1)
      | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f305,f42])).

fof(f305,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(sK2,sK3),sK1)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f304,f28])).

fof(f304,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK4(sK2,sK3),sK1)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f301,f127])).

fof(f301,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK4(sK2,sK3),sK1)
    | sK1 != k1_relat_1(sK3)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(resolution,[],[f162,f21])).

fof(f162,plain,(
    ! [X7] :
      ( ~ v1_funct_1(X7)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X7)
      | r2_hidden(sK4(sK2,X7),sK1)
      | sK1 != k1_relat_1(X7)
      | sK4(sK2,X7) = k1_funct_1(sK2,sK5(sK2,X7))
      | k2_funct_1(sK2) = X7 ) ),
    inference(subsumption_resolution,[],[f161,f25])).

fof(f161,plain,(
    ! [X7] :
      ( r2_hidden(sK4(sK2,X7),sK1)
      | ~ v1_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | sK1 != k1_relat_1(X7)
      | sK4(sK2,X7) = k1_funct_1(sK2,sK5(sK2,X7))
      | k2_funct_1(sK2) = X7 ) ),
    inference(subsumption_resolution,[],[f157,f29])).

fof(f157,plain,(
    ! [X7] :
      ( r2_hidden(sK4(sK2,X7),sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | sK1 != k1_relat_1(X7)
      | sK4(sK2,X7) = k1_funct_1(sK2,sK5(sK2,X7))
      | k2_funct_1(sK2) = X7 ) ),
    inference(superposition,[],[f40,f146])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f465,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3)))
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    inference(resolution,[],[f462,f53])).

% (1752)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f53,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK3,k1_funct_1(sK2,X5)) = X5 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK2,X5) != X4
      | k1_funct_1(sK3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f462,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    inference(resolution,[],[f461,f31])).

fof(f461,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK5(sK2,sK3),sK0)
      | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ) ),
    inference(resolution,[],[f335,f23])).

fof(f335,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
      | r2_hidden(sK5(sK2,sK3),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f334,f42])).

fof(f334,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(sK5(sK2,sK3),sK0)
      | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f332,f42])).

fof(f332,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),sK0)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f331,f28])).

fof(f331,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f328,f127])).

fof(f328,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK1 != k1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(resolution,[],[f180,f21])).

fof(f180,plain,(
    ! [X3] :
      ( ~ v1_funct_1(X3)
      | r2_hidden(sK5(sK2,X3),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X3)
      | sK1 != k1_relat_1(X3)
      | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
      | k2_funct_1(sK2) = X3 ) ),
    inference(forward_demodulation,[],[f179,f146])).

fof(f179,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK2,X3),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k2_relat_1(sK2) != k1_relat_1(X3)
      | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
      | k2_funct_1(sK2) = X3 ) ),
    inference(subsumption_resolution,[],[f178,f25])).

fof(f178,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK2,X3),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k2_relat_1(sK2) != k1_relat_1(X3)
      | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
      | k2_funct_1(sK2) = X3 ) ),
    inference(subsumption_resolution,[],[f169,f29])).

fof(f169,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK2,X3),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k2_relat_1(sK2) != k1_relat_1(X3)
      | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
      | k2_funct_1(sK2) = X3 ) ),
    inference(superposition,[],[f37,f149])).

fof(f149,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f144,f121])).

fof(f121,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f120,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f120,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f119,f31])).

fof(f119,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f30,f50])).

fof(f30,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f144,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f31,f43])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1))
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f859,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f858,f672])).

fof(f858,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f857,f21])).

fof(f857,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f856,f805])).

fof(f805,plain,(
    r2_hidden(sK4(sK2,sK3),sK1) ),
    inference(duplicate_literal_removal,[],[f678])).

fof(f678,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | r2_hidden(sK4(sK2,sK3),sK1) ),
    inference(backward_demodulation,[],[f231,f672])).

fof(f231,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(sK2,sK3)),sK1)
    | r2_hidden(sK4(sK2,sK3),sK1) ),
    inference(resolution,[],[f228,f54])).

fof(f54,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK0)
      | r2_hidden(k1_funct_1(sK2,X5),sK1) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK2,X5) != X4
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f228,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | r2_hidden(sK4(sK2,sK3),sK1) ),
    inference(resolution,[],[f227,f31])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK5(sK2,sK3),sK0)
      | r2_hidden(sK4(sK2,sK3),sK1) ) ),
    inference(resolution,[],[f224,f23])).

fof(f224,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(sK2,sK3),sK1)
      | r2_hidden(sK5(sK2,sK3),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f223,f42])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(sK5(sK2,sK3),sK0)
      | r2_hidden(sK4(sK2,sK3),sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f220,f42])).

fof(f220,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),sK0)
    | r2_hidden(sK4(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f219,f28])).

fof(f219,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK4(sK2,sK3),sK1)
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f216,f127])).

fof(f216,plain,
    ( sK1 != k1_relat_1(sK3)
    | r2_hidden(sK5(sK2,sK3),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK4(sK2,sK3),sK1)
    | sK3 = k2_funct_1(sK2) ),
    inference(resolution,[],[f184,f21])).

fof(f184,plain,(
    ! [X6] :
      ( ~ v1_funct_1(X6)
      | sK1 != k1_relat_1(X6)
      | r2_hidden(sK5(sK2,X6),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X6)
      | r2_hidden(sK4(sK2,X6),sK1)
      | k2_funct_1(sK2) = X6 ) ),
    inference(forward_demodulation,[],[f183,f146])).

fof(f183,plain,(
    ! [X6] :
      ( sK1 != k1_relat_1(X6)
      | r2_hidden(sK5(sK2,X6),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | r2_hidden(sK4(sK2,X6),k2_relat_1(sK2))
      | k2_funct_1(sK2) = X6 ) ),
    inference(forward_demodulation,[],[f182,f146])).

fof(f182,plain,(
    ! [X6] :
      ( r2_hidden(sK5(sK2,X6),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | k2_relat_1(sK2) != k1_relat_1(X6)
      | r2_hidden(sK4(sK2,X6),k2_relat_1(sK2))
      | k2_funct_1(sK2) = X6 ) ),
    inference(subsumption_resolution,[],[f181,f25])).

fof(f181,plain,(
    ! [X6] :
      ( r2_hidden(sK5(sK2,X6),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | k2_relat_1(sK2) != k1_relat_1(X6)
      | r2_hidden(sK4(sK2,X6),k2_relat_1(sK2))
      | k2_funct_1(sK2) = X6 ) ),
    inference(subsumption_resolution,[],[f170,f29])).

fof(f170,plain,(
    ! [X6] :
      ( r2_hidden(sK5(sK2,X6),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | k2_relat_1(sK2) != k1_relat_1(X6)
      | r2_hidden(sK4(sK2,X6),k2_relat_1(sK2))
      | k2_funct_1(sK2) = X6 ) ),
    inference(superposition,[],[f39,f149])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f856,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f852,f127])).

fof(f852,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK3 = k2_funct_1(sK2) ),
    inference(resolution,[],[f851,f177])).

fof(f177,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(sK2,X1),sK0)
      | k1_relat_1(X1) != sK1
      | ~ r2_hidden(sK4(sK2,X1),sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | sK4(sK2,X1) != k1_funct_1(sK2,sK5(sK2,X1))
      | sK5(sK2,X1) != k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1 ) ),
    inference(forward_demodulation,[],[f176,f146])).

fof(f176,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK1
      | ~ r2_hidden(sK5(sK2,X1),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | sK4(sK2,X1) != k1_funct_1(sK2,sK5(sK2,X1))
      | ~ r2_hidden(sK4(sK2,X1),k2_relat_1(sK2))
      | sK5(sK2,X1) != k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1 ) ),
    inference(forward_demodulation,[],[f175,f146])).

fof(f175,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(sK2,X1),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(sK2)
      | sK4(sK2,X1) != k1_funct_1(sK2,sK5(sK2,X1))
      | ~ r2_hidden(sK4(sK2,X1),k2_relat_1(sK2))
      | sK5(sK2,X1) != k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f174,f25])).

fof(f174,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(sK2,X1),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(sK2)
      | sK4(sK2,X1) != k1_funct_1(sK2,sK5(sK2,X1))
      | ~ r2_hidden(sK4(sK2,X1),k2_relat_1(sK2))
      | sK5(sK2,X1) != k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f168,f29])).

fof(f168,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(sK2,X1),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(sK2)
      | sK4(sK2,X1) != k1_funct_1(sK2,sK5(sK2,X1))
      | ~ r2_hidden(sK4(sK2,X1),k2_relat_1(sK2))
      | sK5(sK2,X1) != k1_funct_1(X1,sK4(sK2,X1))
      | k2_funct_1(sK2) = X1 ) ),
    inference(superposition,[],[f34,f149])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | sK4(X0,X1) != k1_funct_1(X0,sK5(X0,X1))
      | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | sK5(X0,X1) != k1_funct_1(X1,sK4(X0,X1))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f851,plain,(
    r2_hidden(sK5(sK2,sK3),sK0) ),
    inference(forward_demodulation,[],[f847,f803])).

fof(f847,plain,(
    r2_hidden(k1_funct_1(sK3,sK4(sK2,sK3)),sK0) ),
    inference(resolution,[],[f805,f52])).

fof(f52,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | r2_hidden(k1_funct_1(sK3,X4),sK0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) != X5
      | r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
