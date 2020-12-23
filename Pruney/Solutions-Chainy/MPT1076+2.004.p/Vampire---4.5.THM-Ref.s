%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 838 expanded)
%              Number of leaves         :   24 ( 380 expanded)
%              Depth                    :   70
%              Number of atoms          :  944 (8012 expanded)
%              Number of equality atoms :  118 ( 987 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(subsumption_resolution,[],[f321,f67])).

fof(f67,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f321,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f58,f320])).

fof(f320,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f319,f108])).

fof(f108,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f53,f52,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                        & v1_partfun1(X4,X0)
                        & m1_subset_1(X5,X1) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                      & v1_partfun1(X4,sK0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
              & v1_funct_2(X3,X1,sK0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                    & v1_partfun1(X4,sK0)
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
            & v1_funct_2(X3,X1,sK0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X3,X2] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                  & v1_partfun1(X4,sK0)
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                & v1_partfun1(X4,sK0)
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
              & v1_partfun1(X4,sK0)
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
            & v1_partfun1(X4,sK0)
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
          & v1_partfun1(sK4,sK0)
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X5] :
        ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
        & v1_partfun1(sK4,sK0)
        & m1_subset_1(X5,sK1) )
   => ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
      & v1_partfun1(sK4,sK0)
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f319,plain,
    ( k1_xboole_0 = sK1
    | ~ v4_relat_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f316,f102])).

fof(f102,plain,(
    r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f101,f58])).

fof(f101,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1) ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f316,plain,
    ( ~ r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK1
    | ~ v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f315,f145])).

fof(f145,plain,(
    v1_partfun1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f144,f57])).

fof(f57,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f144,plain,
    ( v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f143,f59])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f143,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f60])).

fof(f60,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f141,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f72,f61])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f315,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK3,X0)
      | ~ r2_hidden(sK5,X0)
      | k1_xboole_0 = sK1
      | ~ v4_relat_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f314,f109])).

fof(f109,plain,(
    v4_relat_1(sK4,sK0) ),
    inference(resolution,[],[f84,f63])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f314,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(sK5,X0)
      | ~ v4_relat_1(sK4,sK0)
      | ~ v1_partfun1(sK3,X0)
      | ~ v4_relat_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f311,f111])).

fof(f111,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f85,f61])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f311,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ v5_relat_1(sK3,sK0)
      | ~ r2_hidden(sK5,X0)
      | ~ v4_relat_1(sK4,sK0)
      | ~ v1_partfun1(sK3,X0)
      | ~ v4_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f301,f65])).

fof(f65,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK4,X1)
      | k1_xboole_0 = sK1
      | ~ v5_relat_1(sK3,X1)
      | ~ r2_hidden(sK5,X0)
      | ~ v4_relat_1(sK4,X1)
      | ~ v1_partfun1(sK3,X0)
      | ~ v4_relat_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f300,f96])).

fof(f96,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f94,f70])).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f94,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f69,f61])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5,X0)
      | k1_xboole_0 = sK1
      | ~ v5_relat_1(sK3,X1)
      | ~ v1_partfun1(sK4,X1)
      | ~ v4_relat_1(sK4,X1)
      | ~ v1_partfun1(sK3,X0)
      | ~ v4_relat_1(sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f299,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f299,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,k1_relat_1(sK3))
      | k1_xboole_0 = sK1
      | ~ v5_relat_1(sK3,X0)
      | ~ v1_partfun1(sK4,X0)
      | ~ v4_relat_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f298,f97])).

fof(f97,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f95,f70])).

fof(f95,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f69,f63])).

fof(f298,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK3,X0)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(sK5,k1_relat_1(sK3))
      | ~ v1_partfun1(sK4,X0)
      | ~ v4_relat_1(sK4,X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f297,f78])).

fof(f297,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK5,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f296,f96])).

fof(f296,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f295,f111])).

fof(f295,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f294,f59])).

fof(f294,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f293,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f293,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),sK0)
    | ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f291,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f291,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | k1_xboole_0 = sK1
    | ~ v5_relat_1(sK3,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f289,f96])).

fof(f289,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | k1_xboole_0 = sK1
    | ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f288,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f288,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f287,f57])).

fof(f287,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f285,f132])).

fof(f132,plain,(
    v1_funct_2(sK4,sK0,sK2) ),
    inference(subsumption_resolution,[],[f131,f62])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f131,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_2(sK4,sK0,sK2) ),
    inference(subsumption_resolution,[],[f130,f65])).

fof(f130,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(sK4,sK0,sK2) ),
    inference(resolution,[],[f87,f63])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f285,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_2(sK4,sK0,sK2)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f284,f63])).

fof(f284,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f282,f63])).

fof(f282,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    inference(superposition,[],[f280,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f280,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f279,f59])).

fof(f279,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f278,f60])).

fof(f278,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f277,f61])).

fof(f277,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f276,f62])).

fof(f276,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f275,f63])).

fof(f275,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f273,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f273,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f271,f61])).

fof(f271,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4))
      | k1_xboole_0 = sK1
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    inference(superposition,[],[f270,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f270,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | k1_xboole_0 = sK1
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f269,f59])).

fof(f269,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f268,f60])).

fof(f268,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f267,f61])).

fof(f267,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f266,f62])).

fof(f266,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f265,f63])).

fof(f265,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f264,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f264,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f263,f59])).

fof(f263,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f262,f60])).

fof(f262,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f261,f61])).

fof(f261,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f260,f62])).

fof(f260,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f258,f63])).

fof(f258,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f253,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f253,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f252,f125])).

fof(f125,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f124,f57])).

fof(f124,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f65])).

fof(f123,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f77,f63])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f252,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f251,f62])).

fof(f251,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,(
    ! [X0] :
      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
      | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
      | ~ m1_subset_1(k1_funct_1(sK3,sK5),X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_funct_2(sK4,X0,sK2)
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f245,f183])).

fof(f183,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_funct_1(X6,X7) = k7_partfun1(X5,X6,X7)
      | ~ m1_subset_1(X7,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(X6,X4,X5)
      | ~ v1_funct_1(X6)
      | v1_xboole_0(X5)
      | v1_xboole_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_funct_1(X6,X7) = k7_partfun1(X5,X6,X7)
      | ~ m1_subset_1(X7,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(X6,X4,X5)
      | ~ v1_funct_1(X6)
      | v1_xboole_0(X5)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X7,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(X6,X4,X5)
      | ~ v1_funct_1(X6)
      | v1_xboole_0(X4) ) ),
    inference(superposition,[],[f68,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

fof(f245,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f244,f57])).

fof(f244,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f243,f59])).

fof(f243,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f242,f60])).

fof(f242,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f241,f61])).

fof(f241,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f240,f62])).

fof(f240,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f239,f63])).

fof(f239,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f222,f64])).

fof(f222,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f177,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f177,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f176,f58])).

fof(f176,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f175,f59])).

fof(f175,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f174,f60])).

fof(f174,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f173,f61])).

fof(f173,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f172,f64])).

fof(f172,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f171,f88])).

fof(f171,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f170,f58])).

fof(f170,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f169,f64])).

fof(f169,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f66,f88])).

fof(f66,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f58,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:32:06 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.43  % (2322)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.44  % (2322)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f346,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f321,f67])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.44  fof(f321,plain,(
% 0.21/0.44    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(backward_demodulation,[],[f58,f320])).
% 0.21/0.44  fof(f320,plain,(
% 0.21/0.44    k1_xboole_0 = sK1),
% 0.21/0.44    inference(subsumption_resolution,[],[f319,f108])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    v4_relat_1(sK3,sK1)),
% 0.21/0.44    inference(resolution,[],[f84,f61])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f53,f52,f51,f50,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) => (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f19])).
% 0.21/0.44  fof(f19,conjecture,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.44  fof(f319,plain,(
% 0.21/0.44    k1_xboole_0 = sK1 | ~v4_relat_1(sK3,sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f316,f102])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    r2_hidden(sK5,sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f101,f58])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    v1_xboole_0(sK1) | r2_hidden(sK5,sK1)),
% 0.21/0.44    inference(resolution,[],[f76,f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    m1_subset_1(sK5,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.44  fof(f316,plain,(
% 0.21/0.44    ~r2_hidden(sK5,sK1) | k1_xboole_0 = sK1 | ~v4_relat_1(sK3,sK1)),
% 0.21/0.44    inference(resolution,[],[f315,f145])).
% 0.21/0.44  fof(f145,plain,(
% 0.21/0.44    v1_partfun1(sK3,sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f144,f57])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ~v1_xboole_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    v1_partfun1(sK3,sK1) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f143,f59])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    v1_funct_1(sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    ~v1_funct_1(sK3) | v1_partfun1(sK3,sK1) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f141,f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_partfun1(sK3,sK1) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f72,f61])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.44    inference(flattening,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.44  fof(f315,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_partfun1(sK3,X0) | ~r2_hidden(sK5,X0) | k1_xboole_0 = sK1 | ~v4_relat_1(sK3,X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f314,f109])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    v4_relat_1(sK4,sK0)),
% 0.21/0.44    inference(resolution,[],[f84,f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  fof(f314,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(sK5,X0) | ~v4_relat_1(sK4,sK0) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f311,f111])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    v5_relat_1(sK3,sK0)),
% 0.21/0.44    inference(resolution,[],[f85,f61])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  fof(f311,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = sK1 | ~v5_relat_1(sK3,sK0) | ~r2_hidden(sK5,X0) | ~v4_relat_1(sK4,sK0) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) )),
% 0.21/0.44    inference(resolution,[],[f301,f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    v1_partfun1(sK4,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  fof(f301,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_partfun1(sK4,X1) | k1_xboole_0 = sK1 | ~v5_relat_1(sK3,X1) | ~r2_hidden(sK5,X0) | ~v4_relat_1(sK4,X1) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f300,f96])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    v1_relat_1(sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f94,f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.21/0.44    inference(resolution,[],[f69,f61])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.44  fof(f300,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(sK5,X0) | k1_xboole_0 = sK1 | ~v5_relat_1(sK3,X1) | ~v1_partfun1(sK4,X1) | ~v4_relat_1(sK4,X1) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) )),
% 0.21/0.44    inference(superposition,[],[f299,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.44  fof(f299,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(sK5,k1_relat_1(sK3)) | k1_xboole_0 = sK1 | ~v5_relat_1(sK3,X0) | ~v1_partfun1(sK4,X0) | ~v4_relat_1(sK4,X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f298,f97])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    v1_relat_1(sK4)),
% 0.21/0.44    inference(subsumption_resolution,[],[f95,f70])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK0,sK2))),
% 0.21/0.44    inference(resolution,[],[f69,f63])).
% 0.21/0.44  fof(f298,plain,(
% 0.21/0.44    ( ! [X0] : (~v5_relat_1(sK3,X0) | k1_xboole_0 = sK1 | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_partfun1(sK4,X0) | ~v4_relat_1(sK4,X0) | ~v1_relat_1(sK4)) )),
% 0.21/0.44    inference(superposition,[],[f297,f78])).
% 0.21/0.44  fof(f297,plain,(
% 0.21/0.44    ~v5_relat_1(sK3,k1_relat_1(sK4)) | k1_xboole_0 = sK1 | ~r2_hidden(sK5,k1_relat_1(sK3))),
% 0.21/0.44    inference(subsumption_resolution,[],[f296,f96])).
% 0.21/0.44  fof(f296,plain,(
% 0.21/0.44    ~v5_relat_1(sK3,k1_relat_1(sK4)) | k1_xboole_0 = sK1 | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f295,f111])).
% 0.21/0.44  fof(f295,plain,(
% 0.21/0.44    ~v5_relat_1(sK3,k1_relat_1(sK4)) | k1_xboole_0 = sK1 | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f294,f59])).
% 0.21/0.44  fof(f294,plain,(
% 0.21/0.44    ~v5_relat_1(sK3,k1_relat_1(sK4)) | k1_xboole_0 = sK1 | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3)),
% 0.21/0.44    inference(resolution,[],[f293,f80])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.44  fof(f293,plain,(
% 0.21/0.44    ~r2_hidden(k1_funct_1(sK3,sK5),sK0) | ~v5_relat_1(sK3,k1_relat_1(sK4)) | k1_xboole_0 = sK1),
% 0.21/0.44    inference(resolution,[],[f291,f75])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.44  fof(f291,plain,(
% 0.21/0.44    ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | k1_xboole_0 = sK1 | ~v5_relat_1(sK3,k1_relat_1(sK4))),
% 0.21/0.44    inference(subsumption_resolution,[],[f289,f96])).
% 0.21/0.44  fof(f289,plain,(
% 0.21/0.44    ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | k1_xboole_0 = sK1 | ~v5_relat_1(sK3,k1_relat_1(sK4)) | ~v1_relat_1(sK3)),
% 0.21/0.44    inference(resolution,[],[f288,f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.44  fof(f288,plain,(
% 0.21/0.44    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | k1_xboole_0 = sK1),
% 0.21/0.44    inference(subsumption_resolution,[],[f287,f57])).
% 0.21/0.44  fof(f287,plain,(
% 0.21/0.44    k1_xboole_0 = sK1 | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f285,f132])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    v1_funct_2(sK4,sK0,sK2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f131,f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    v1_funct_1(sK4)),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    ~v1_funct_1(sK4) | v1_funct_2(sK4,sK0,sK2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f130,f65])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    ~v1_partfun1(sK4,sK0) | ~v1_funct_1(sK4) | v1_funct_2(sK4,sK0,sK2)),
% 0.21/0.44    inference(resolution,[],[f87,f63])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(flattening,[],[f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.44  fof(f285,plain,(
% 0.21/0.44    k1_xboole_0 = sK1 | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f284,f63])).
% 0.21/0.44  fof(f284,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | k1_xboole_0 = sK1 | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f282,f63])).
% 0.21/0.44  fof(f282,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | k1_xboole_0 = sK1 | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))) )),
% 0.21/0.44    inference(superposition,[],[f280,f83])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.44  fof(f280,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f279,f59])).
% 0.21/0.44  fof(f279,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f278,f60])).
% 0.21/0.44  fof(f278,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f277,f61])).
% 0.21/0.44  fof(f277,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f276,f62])).
% 0.21/0.44  fof(f276,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f275,f63])).
% 0.21/0.44  fof(f275,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(resolution,[],[f273,f89])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.44    inference(flattening,[],[f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.44    inference(ennf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.21/0.44  fof(f273,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f271,f61])).
% 0.21/0.44  fof(f271,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) )),
% 0.21/0.44    inference(superposition,[],[f270,f82])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.44  fof(f270,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | k1_xboole_0 = sK1 | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f269,f59])).
% 0.21/0.44  fof(f269,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f268,f60])).
% 0.21/0.44  fof(f268,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f267,f61])).
% 0.21/0.44  fof(f267,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f266,f62])).
% 0.21/0.44  fof(f266,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f265,f63])).
% 0.21/0.44  fof(f265,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(resolution,[],[f264,f90])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f48])).
% 0.21/0.44  fof(f264,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f263,f59])).
% 0.21/0.44  fof(f263,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f262,f60])).
% 0.21/0.44  fof(f262,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f261,f61])).
% 0.21/0.44  fof(f261,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f260,f62])).
% 0.21/0.44  fof(f260,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f258,f63])).
% 0.21/0.44  fof(f258,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)) )),
% 0.21/0.44    inference(resolution,[],[f253,f91])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f48])).
% 0.21/0.44  fof(f253,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f252,f125])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    ~v1_xboole_0(sK2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f124,f57])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    ~v1_xboole_0(sK2) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f123,f65])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    ~v1_partfun1(sK4,sK0) | ~v1_xboole_0(sK2) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f77,f63])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.21/0.44  fof(f252,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f251,f62])).
% 0.21/0.44  fof(f251,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | ~v1_funct_1(sK4) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f250])).
% 0.21/0.44  fof(f250,plain,(
% 0.21/0.44    ( ! [X0] : (k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(k1_funct_1(sK3,sK5),X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(sK4,X0,sK2) | ~v1_funct_1(sK4) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(superposition,[],[f245,f183])).
% 0.21/0.44  fof(f183,plain,(
% 0.21/0.44    ( ! [X6,X4,X7,X5] : (k1_funct_1(X6,X7) = k7_partfun1(X5,X6,X7) | ~m1_subset_1(X7,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(X6,X4,X5) | ~v1_funct_1(X6) | v1_xboole_0(X5) | v1_xboole_0(X4)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f178])).
% 0.21/0.44  fof(f178,plain,(
% 0.21/0.44    ( ! [X6,X4,X7,X5] : (k1_funct_1(X6,X7) = k7_partfun1(X5,X6,X7) | ~m1_subset_1(X7,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(X6,X4,X5) | ~v1_funct_1(X6) | v1_xboole_0(X5) | v1_xboole_0(X4) | ~m1_subset_1(X7,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(X6,X4,X5) | ~v1_funct_1(X6) | v1_xboole_0(X4)) )),
% 0.21/0.44    inference(superposition,[],[f68,f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,axiom,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).
% 0.21/0.44  fof(f245,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))),
% 0.21/0.44    inference(subsumption_resolution,[],[f244,f57])).
% 0.21/0.44  fof(f244,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f243,f59])).
% 0.21/0.44  fof(f243,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f242,f60])).
% 0.21/0.44  fof(f242,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f241,f61])).
% 0.21/0.44  fof(f241,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f240,f62])).
% 0.21/0.44  fof(f240,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f239,f63])).
% 0.21/0.44  fof(f239,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f222,f64])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(superposition,[],[f177,f81])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.44    inference(flattening,[],[f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.44  fof(f177,plain,(
% 0.21/0.44    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 0.21/0.44    inference(subsumption_resolution,[],[f176,f58])).
% 0.21/0.44  fof(f176,plain,(
% 0.21/0.44    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | v1_xboole_0(sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f175,f59])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f174,f60])).
% 0.21/0.44  fof(f174,plain,(
% 0.21/0.44    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f173,f61])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f172,f64])).
% 0.21/0.44  fof(f172,plain,(
% 0.21/0.44    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)),
% 0.21/0.44    inference(superposition,[],[f171,f88])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 0.21/0.44    inference(subsumption_resolution,[],[f170,f58])).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | v1_xboole_0(sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f169,f64])).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | v1_xboole_0(sK1)),
% 0.21/0.44    inference(superposition,[],[f66,f88])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ~v1_xboole_0(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f54])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (2322)------------------------------
% 0.21/0.44  % (2322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (2322)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (2322)Memory used [KB]: 1918
% 0.21/0.44  % (2322)Time elapsed: 0.019 s
% 0.21/0.44  % (2322)------------------------------
% 0.21/0.44  % (2322)------------------------------
% 0.21/0.45  % (2302)Success in time 0.083 s
%------------------------------------------------------------------------------
