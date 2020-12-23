%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t173_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:36 EDT 2019

% Result     : Theorem 109.17s
% Output     : Refutation 109.17s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 668 expanded)
%              Number of leaves         :   20 ( 290 expanded)
%              Depth                    :   40
%              Number of atoms          :  734 (8628 expanded)
%              Number of equality atoms :  148 (1473 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10866,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8743,f109])).

fof(f109,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',dt_o_0_0_xboole_0)).

fof(f8743,plain,(
    ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f8742,f98])).

fof(f98,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( k2_partfun1(sK0,sK1,sK2,sK3) != sK4
    & ! [X5] :
        ( k3_funct_2(sK0,sK1,sK2,X5) = k1_funct_1(sK4,X5)
        | ~ r2_hidden(X5,sK3)
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK4,sK3,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f38,f82,f81,f80,f79,f78])).

fof(f78,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k2_partfun1(X0,X1,X2,X3) != X4
                        & ! [X5] :
                            ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                            | ~ r2_hidden(X5,X3)
                            | ~ m1_subset_1(X5,X0) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(sK0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(sK0,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,sK0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,X0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k2_partfun1(X0,sK1,X2,X3) != X4
                    & ! [X5] :
                        ( k3_funct_2(X0,sK1,X2,X5) = k1_funct_1(X4,X5)
                        | ~ r2_hidden(X5,X3)
                        | ~ m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                    & v1_funct_2(X4,X3,sK1)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
            & v1_funct_2(X2,X0,sK1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k2_partfun1(X0,X1,X2,X3) != X4
                  & ! [X5] :
                      ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                      | ~ r2_hidden(X5,X3)
                      | ~ m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                  & v1_funct_2(X4,X3,X1)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k2_partfun1(X0,X1,sK2,X3) != X4
                & ! [X5] :
                    ( k3_funct_2(X0,X1,sK2,X5) = k1_funct_1(X4,X5)
                    | ~ r2_hidden(X5,X3)
                    | ~ m1_subset_1(X5,X0) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                & v1_funct_2(X4,X3,X1)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK2,X0,X1)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k2_partfun1(X0,X1,X2,X3) != X4
              & ! [X5] :
                  ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                  | ~ r2_hidden(X5,X3)
                  | ~ m1_subset_1(X5,X0) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
              & v1_funct_2(X4,X3,X1)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(X0))
          & ~ v1_xboole_0(X3) )
     => ( ? [X4] :
            ( k2_partfun1(X0,X1,X2,sK3) != X4
            & ! [X5] :
                ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                | ~ r2_hidden(X5,sK3)
                | ~ m1_subset_1(X5,X0) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
            & v1_funct_2(X4,sK3,X1)
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_partfun1(X0,X1,X2,X3) != X4
          & ! [X5] :
              ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
              | ~ r2_hidden(X5,X3)
              | ~ m1_subset_1(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X4,X3,X1)
          & v1_funct_1(X4) )
     => ( k2_partfun1(X0,X1,X2,X3) != sK4
        & ! [X5] :
            ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(sK4,X5)
            | ~ r2_hidden(X5,X3)
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK4,X3,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,X0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,X0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X4,X3,X1)
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,X0)
                             => ( r2_hidden(X5,X3)
                               => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                         => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t173_funct_2)).

fof(f8742,plain,(
    o_0_0_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f8741,f103])).

fof(f103,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f83])).

fof(f8741,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f8740,f101])).

fof(f101,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

fof(f8740,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | o_0_0_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f8672,f100])).

fof(f100,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f83])).

fof(f8672,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,X0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f8670,f99])).

fof(f99,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f8670,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ v1_funct_2(sK2,X0,sK1)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f8668])).

fof(f8668,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ v1_funct_2(sK2,X0,sK1)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f8665,f351])).

fof(f351,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f350])).

fof(f350,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f296,f141])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',redefinition_k2_partfun1)).

fof(f296,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X1,X0,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | o_0_0_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f152,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t3_subset)).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X0)
      | o_0_0_xboole_0 = X1
      | m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f139,f110])).

fof(f110,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',d2_xboole_0)).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t38_funct_2)).

fof(f8665,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | o_0_0_xboole_0 = sK1 ),
    inference(resolution,[],[f8655,f101])).

fof(f8655,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1 ) ),
    inference(resolution,[],[f8646,f101])).

fof(f8646,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f8645,f99])).

fof(f8645,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f8644,f218])).

fof(f218,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k7_relat_1(X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k7_relat_1(X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f142,f141])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',dt_k2_partfun1)).

fof(f8644,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f8643,f103])).

fof(f8643,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ v1_funct_1(k7_relat_1(sK2,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f8642])).

fof(f8642,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ v1_funct_1(k7_relat_1(sK2,sK3))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f8639,f347])).

fof(f347,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK2,X0),X0,sK1)
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f346,f99])).

fof(f346,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK2,X0),X0,sK1)
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f344,f101])).

fof(f344,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK2,X0),X0,sK1)
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f335,f141])).

fof(f335,plain,(
    ! [X0] :
      ( v1_funct_2(k2_partfun1(sK0,sK1,sK2,X0),X0,sK1)
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f334,f99])).

fof(f334,plain,(
    ! [X0] :
      ( v1_funct_2(k2_partfun1(sK0,sK1,sK2,X0),X0,sK1)
      | o_0_0_xboole_0 = sK1
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f332,f101])).

fof(f332,plain,(
    ! [X0] :
      ( v1_funct_2(k2_partfun1(sK0,sK1,sK2,X0),X0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f293,f100])).

fof(f293,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X1,X0)
      | v1_funct_2(k2_partfun1(X1,X0,X2,X3),X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | o_0_0_xboole_0 = X0
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f154,f123])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X0)
      | o_0_0_xboole_0 = X1
      | v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f137,f110])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f8639,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ v1_funct_1(k7_relat_1(sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f8638,f220])).

fof(f220,plain,(
    k7_relat_1(sK2,sK3) != sK4 ),
    inference(subsumption_resolution,[],[f219,f99])).

fof(f219,plain,
    ( k7_relat_1(sK2,sK3) != sK4
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f216,f101])).

fof(f216,plain,
    ( k7_relat_1(sK2,sK3) != sK4
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f108,f141])).

fof(f108,plain,(
    k2_partfun1(sK0,sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f83])).

fof(f8638,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,sK1)
      | ~ v1_funct_1(k7_relat_1(sK2,sK3))
      | k7_relat_1(sK2,sK3) = sK4 ) ),
    inference(duplicate_literal_removal,[],[f8637])).

fof(f8637,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,sK1)
      | ~ v1_funct_1(k7_relat_1(sK2,sK3))
      | k7_relat_1(sK2,sK3) = sK4 ) ),
    inference(resolution,[],[f8636,f410])).

fof(f410,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK3,X0,sK4),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_2(X0,sK3,sK1)
      | ~ v1_funct_1(X0)
      | sK4 = X0 ) ),
    inference(subsumption_resolution,[],[f409,f106])).

fof(f106,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f83])).

fof(f409,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | m1_subset_1(sK8(sK3,X0,sK4),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_2(X0,sK3,sK1)
      | ~ v1_funct_1(X0)
      | sK4 = X0 ) ),
    inference(resolution,[],[f373,f105])).

fof(f105,plain,(
    v1_funct_2(sK4,sK3,sK1) ),
    inference(cnf_transformation,[],[f83])).

fof(f373,plain,(
    ! [X26,X24,X25] :
      ( ~ v1_funct_2(sK4,X24,X25)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | m1_subset_1(sK8(X24,X26,sK4),X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ v1_funct_2(X26,X24,X25)
      | ~ v1_funct_1(X26)
      | sK4 = X26 ) ),
    inference(resolution,[],[f300,f104])).

fof(f104,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

fof(f300,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_2(X2,X0,X3)
      | m1_subset_1(sK8(X0,X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_2(X1,X0,X3)
      | ~ v1_funct_1(X1)
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_2(X2,X0,X3)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_2(X1,X0,X3)
      | ~ v1_funct_1(X1)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(resolution,[],[f129,f146])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',redefinition_r2_relset_1)).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | m1_subset_1(sK8(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK8(X0,X2,X3)) != k1_funct_1(X3,sK8(X0,X2,X3))
            & m1_subset_1(sK8(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f58,f92])).

fof(f92,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK8(X0,X2,X3)) != k1_funct_1(X3,sK8(X0,X2,X3))
        & m1_subset_1(sK8(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t113_funct_2)).

fof(f8636,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK8(sK3,k7_relat_1(sK2,sK3),sK4),sK3)
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ) ),
    inference(subsumption_resolution,[],[f8635,f305])).

fof(f305,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(sK4,X0)
      | ~ m1_subset_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f304,f212])).

fof(f212,plain,(
    ! [X5] :
      ( m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(subsumption_resolution,[],[f208,f102])).

fof(f102,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f208,plain,(
    ! [X5] :
      ( m1_subset_1(X5,sK0)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(resolution,[],[f174,f103])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f131,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t2_subset)).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t4_subset)).

fof(f304,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK4,X0)
      | ~ m1_subset_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f303,f102])).

fof(f303,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK4,X0)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X0,sK3) ) ),
    inference(resolution,[],[f290,f118])).

fof(f290,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X1,sK0)
      | k1_funct_1(sK2,X1) = k1_funct_1(sK4,X1) ) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,X1) = k1_funct_1(sK4,X1)
      | ~ m1_subset_1(X1,sK0)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(superposition,[],[f281,f107])).

fof(f107,plain,(
    ! [X5] :
      ( k3_funct_2(sK0,sK1,sK2,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,sK3)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f281,plain,(
    ! [X0] :
      ( k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f280,f97])).

fof(f97,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f280,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f279,f99])).

fof(f279,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f277,f101])).

fof(f277,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f134,f100])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',redefinition_k3_funct_2)).

fof(f8635,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(sK2,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4))
      | ~ m1_subset_1(sK8(sK3,k7_relat_1(sK2,sK3),sK4),sK3) ) ),
    inference(subsumption_resolution,[],[f8634,f102])).

fof(f8634,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(sK2,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK8(sK3,k7_relat_1(sK2,sK3),sK4),sK3) ) ),
    inference(resolution,[],[f2323,f118])).

fof(f2323,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(sK3,k7_relat_1(sK2,sK3),sK4),sK3)
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(sK2,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) ) ),
    inference(subsumption_resolution,[],[f2322,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',cc1_relset_1)).

fof(f2322,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK2,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(sK8(sK3,k7_relat_1(sK2,sK3),sK4),sK3)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f2321,f99])).

fof(f2321,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK2,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(sK8(sK3,k7_relat_1(sK2,sK3),sK4),sK3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f1048,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t72_funct_1)).

fof(f1048,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(k7_relat_1(sK2,sK3),sK8(sK3,k7_relat_1(sK2,sK3),sK4))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f1047,f99])).

fof(f1047,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(k7_relat_1(sK2,sK3),sK8(sK3,k7_relat_1(sK2,sK3),sK4))
      | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | o_0_0_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f603,f218])).

fof(f603,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(k7_relat_1(sK2,sK3),sK8(sK3,k7_relat_1(sK2,sK3),sK4))
    | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | o_0_0_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f602,f103])).

fof(f602,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(k7_relat_1(sK2,sK3),sK8(sK3,k7_relat_1(sK2,sK3),sK4))
    | ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | o_0_0_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f597,f220])).

fof(f597,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k1_funct_1(sK4,sK8(sK3,k7_relat_1(sK2,sK3),sK4)) != k1_funct_1(k7_relat_1(sK2,sK3),sK8(sK3,k7_relat_1(sK2,sK3),sK4))
    | ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | k7_relat_1(sK2,sK3) = sK4
    | o_0_0_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f440,f347])).

fof(f440,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | k1_funct_1(sK4,sK8(sK3,X0,sK4)) != k1_funct_1(X0,sK8(sK3,X0,sK4))
      | ~ v1_funct_1(X0)
      | sK4 = X0 ) ),
    inference(subsumption_resolution,[],[f439,f106])).

fof(f439,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | k1_funct_1(sK4,sK8(sK3,X0,sK4)) != k1_funct_1(X0,sK8(sK3,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_2(X0,sK3,sK1)
      | ~ v1_funct_1(X0)
      | sK4 = X0 ) ),
    inference(resolution,[],[f385,f105])).

fof(f385,plain,(
    ! [X26,X24,X25] :
      ( ~ v1_funct_2(sK4,X24,X25)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k1_funct_1(sK4,sK8(X24,X26,sK4)) != k1_funct_1(X26,sK8(X24,X26,sK4))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ v1_funct_2(X26,X24,X25)
      | ~ v1_funct_1(X26)
      | sK4 = X26 ) ),
    inference(resolution,[],[f302,f104])).

fof(f302,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_2(X2,X1,X3)
      | k1_funct_1(X0,sK8(X1,X0,X2)) != k1_funct_1(X2,sK8(X1,X0,X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_2(X0,X1,X3)
      | ~ v1_funct_1(X0)
      | X0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X0,sK8(X1,X0,X2)) != k1_funct_1(X2,sK8(X1,X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_2(X2,X1,X3)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_2(X0,X1,X3)
      | ~ v1_funct_1(X0)
      | X0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(resolution,[],[f130,f146])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK8(X0,X2,X3)) != k1_funct_1(X3,sK8(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f93])).
%------------------------------------------------------------------------------
