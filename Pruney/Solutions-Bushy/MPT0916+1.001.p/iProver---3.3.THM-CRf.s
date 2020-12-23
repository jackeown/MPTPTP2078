%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0916+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:24 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  215 (370673 expanded)
%              Number of clauses        :  143 (117655 expanded)
%              Number of leaves         :   22 (112696 expanded)
%              Depth                    :   51
%              Number of atoms          :  808 (1904676 expanded)
%              Number of equality atoms :  577 (555936 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f28])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
            | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
            | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
          & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5)
          | ~ r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4)
          | ~ r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3) )
        & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5))
        & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
              & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X2)) )
     => ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6)
              | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
              | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
            & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6))
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & m1_subset_1(sK6,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5)
                  | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5))
                & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK5,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
                  & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f27,f35,f34,f33,f32])).

fof(f59,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ~ ( ? [X6] :
            ( ? [X7] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                    & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                    & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                & X6 = X7
                & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ! [X6] :
          ( ! [X7] :
              ( ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
              | X6 != X7
              | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
          | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f37,f37,f37,f37,f37,f37])).

fof(f72,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X7) = k7_mcart_1(X3,X4,X5,X7)
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X7,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f66])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f37])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f37,f37,f37,f37,f37,f37])).

fof(f74,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X7) = k5_mcart_1(X3,X4,X5,X7)
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X7,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f68])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f37,f37,f37,f37,f37,f37])).

fof(f73,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X7) = k6_mcart_1(X3,X4,X5,X7)
      | ~ m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))
      | ~ m1_subset_1(X7,k3_zfmisc_1(X0,X1,X2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f67])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f46,f37,f37])).

fof(f71,plain,(
    ! [X2,X1] : o_0_0_xboole_0 = k3_zfmisc_1(o_0_0_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f63])).

fof(f56,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != X1
      | o_0_0_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f47,f37,f37])).

fof(f70,plain,(
    ! [X2,X0] : o_0_0_xboole_0 = k3_zfmisc_1(X0,o_0_0_xboole_0,X2) ),
    inference(equality_resolution,[],[f62])).

fof(f57,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != X2
      | o_0_0_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f48,f37,f37])).

fof(f69,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k3_zfmisc_1(X0,X1,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_645,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_643,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2202,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_643])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_635,plain,
    ( r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_644,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1528,plain,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_644])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_634,plain,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | ~ m1_subset_1(X0,k3_zfmisc_1(X4,X5,X6))
    | k7_mcart_1(X1,X2,X3,X0) = k7_mcart_1(X4,X5,X6,X0)
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_640,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k7_mcart_1(X4,X5,X6,X3)
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X4
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top
    | m1_subset_1(X3,k3_zfmisc_1(X4,X5,X6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3889,plain,
    ( k7_mcart_1(X0,X1,X2,sK7) = k7_mcart_1(sK1,sK2,sK3,sK7)
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_640])).

cnf(c_4230,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = k7_mcart_1(sK1,sK2,sK3,sK7)
    | sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1528,c_3889])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_647,plain,
    ( m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2201,plain,
    ( r2_hidden(k7_mcart_1(X0,X1,X2,X3),X2) = iProver_top
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_643])).

cnf(c_4413,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) = iProver_top
    | m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4230,c_2201])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_56,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_294,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_970,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_999,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1145,plain,
    ( ~ v1_xboole_0(sK5)
    | o_0_0_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1146,plain,
    ( o_0_0_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_1363,plain,
    ( ~ v1_xboole_0(sK4)
    | o_0_0_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1364,plain,
    ( o_0_0_xboole_0 = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1363])).

cnf(c_301,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1595,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_1601,plain,
    ( sK6 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1595])).

cnf(c_1603,plain,
    ( sK6 != o_0_0_xboole_0
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | ~ m1_subset_1(X0,k3_zfmisc_1(X4,X5,X6))
    | k5_mcart_1(X1,X2,X3,X0) = k5_mcart_1(X4,X5,X6,X0)
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_638,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k5_mcart_1(X4,X5,X6,X3)
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X4
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top
    | m1_subset_1(X3,k3_zfmisc_1(X4,X5,X6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2082,plain,
    ( k5_mcart_1(X0,X1,X2,sK7) = k5_mcart_1(sK1,sK2,sK3,sK7)
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_638])).

cnf(c_3591,plain,
    ( k5_mcart_1(sK4,sK5,sK6,sK7) = k5_mcart_1(sK1,sK2,sK3,sK7)
    | sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1528,c_2082])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_649,plain,
    ( m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4297,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) = iProver_top
    | m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3591,c_649])).

cnf(c_27,plain,
    ( r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_822,plain,
    ( ~ r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    | m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_823,plain,
    ( r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) != iProver_top
    | m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_4720,plain,
    ( m1_subset_1(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) = iProver_top
    | sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4297,c_27,c_823])).

cnf(c_4721,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_4720])).

cnf(c_4731,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4721,c_643])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | ~ m1_subset_1(X0,k3_zfmisc_1(X4,X5,X6))
    | k6_mcart_1(X1,X2,X3,X0) = k6_mcart_1(X4,X5,X6,X0)
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_639,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k6_mcart_1(X4,X5,X6,X3)
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X4
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top
    | m1_subset_1(X3,k3_zfmisc_1(X4,X5,X6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2399,plain,
    ( k6_mcart_1(X0,X1,X2,sK7) = k6_mcart_1(sK1,sK2,sK3,sK7)
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_639])).

cnf(c_4167,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) = k6_mcart_1(sK1,sK2,sK3,sK7)
    | sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1528,c_2399])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_648,plain,
    ( m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4342,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) = iProver_top
    | m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4167,c_648])).

cnf(c_4896,plain,
    ( m1_subset_1(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) = iProver_top
    | sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4342,c_27,c_823])).

cnf(c_4897,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_4896])).

cnf(c_4907,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4897,c_643])).

cnf(c_4390,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) = iProver_top
    | m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4230,c_647])).

cnf(c_4910,plain,
    ( m1_subset_1(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) = iProver_top
    | sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4390,c_27,c_823])).

cnf(c_4911,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_4910])).

cnf(c_4921,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4911,c_643])).

cnf(c_295,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1486,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_5611,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_5612,plain,
    ( sK5 != sK5
    | sK5 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_5611])).

cnf(c_1521,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_5624,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1521])).

cnf(c_5625,plain,
    ( sK4 != sK4
    | sK4 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_5624])).

cnf(c_5646,plain,
    ( sK5 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4413,c_28,c_56,c_970,c_999,c_1146,c_1364,c_1603,c_4731,c_4907,c_4921,c_5612,c_5625])).

cnf(c_5647,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_5646])).

cnf(c_641,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5656,plain,
    ( sK4 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_5647,c_641])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_631,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5914,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5656,c_631])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_637,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1358,plain,
    ( v1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_637])).

cnf(c_5912,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(k3_zfmisc_1(o_0_0_xboole_0,sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5656,c_1358])).

cnf(c_9,plain,
    ( k3_zfmisc_1(o_0_0_xboole_0,X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5946,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5912,c_9])).

cnf(c_6031,plain,
    ( sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK5 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5914,c_56,c_5946])).

cnf(c_6032,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_6031])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_632,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6048,plain,
    ( sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6032,c_632])).

cnf(c_6046,plain,
    ( sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(k3_zfmisc_1(sK4,o_0_0_xboole_0,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6032,c_1358])).

cnf(c_8,plain,
    ( k3_zfmisc_1(X0,o_0_0_xboole_0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6075,plain,
    ( sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6046,c_8])).

cnf(c_6305,plain,
    ( sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6048,c_56,c_6075])).

cnf(c_6306,plain,
    ( sK6 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_6305])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_633,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6321,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6306,c_633])).

cnf(c_6318,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(k3_zfmisc_1(sK4,sK5,o_0_0_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6306,c_1358])).

cnf(c_7,plain,
    ( k3_zfmisc_1(X0,X1,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6355,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6318,c_7])).

cnf(c_6394,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6355])).

cnf(c_6397,plain,
    ( sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6321,c_56,c_6355])).

cnf(c_6398,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_6397])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_642,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2327,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_633,c_642])).

cnf(c_4007,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_2327])).

cnf(c_6404,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6398,c_4007])).

cnf(c_6907,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_6913,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6907])).

cnf(c_6915,plain,
    ( sK3 != o_0_0_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6913])).

cnf(c_7081,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6404,c_56,c_4007,c_6398,c_6915])).

cnf(c_7082,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_7081])).

cnf(c_7089,plain,
    ( sK6 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_7082,c_641])).

cnf(c_6409,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6398,c_633])).

cnf(c_6690,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6409,c_642])).

cnf(c_7132,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6690,c_56,c_2327,c_6398,c_6915])).

cnf(c_7133,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_7132])).

cnf(c_7254,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7089,c_7133])).

cnf(c_7268,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7089,c_635])).

cnf(c_7279,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(sK7,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7268,c_7])).

cnf(c_7348,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7254,c_7279])).

cnf(c_7384,plain,
    ( sK1 = o_0_0_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7348,c_632])).

cnf(c_7511,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7384,c_642])).

cnf(c_7529,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | sK1 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7511,c_56])).

cnf(c_7530,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_7529])).

cnf(c_7541,plain,
    ( sK1 = o_0_0_xboole_0
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_7530])).

cnf(c_7603,plain,
    ( sK5 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_7541,c_641])).

cnf(c_7637,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7603,c_7530])).

cnf(c_7650,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(sK7,k3_zfmisc_1(sK4,o_0_0_xboole_0,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7603,c_635])).

cnf(c_7658,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(sK7,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7650,c_8])).

cnf(c_7697,plain,
    ( sK1 = o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7637,c_7658])).

cnf(c_2329,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_631,c_642])).

cnf(c_7791,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7697,c_2329])).

cnf(c_6731,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_6737,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6731])).

cnf(c_6739,plain,
    ( sK1 != o_0_0_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6737])).

cnf(c_7853,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7791,c_56,c_2329,c_6739,c_7697])).

cnf(c_7863,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_7853])).

cnf(c_8243,plain,
    ( sK4 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_7863,c_641])).

cnf(c_8355,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8243,c_7853])).

cnf(c_8363,plain,
    ( r2_hidden(sK7,k3_zfmisc_1(o_0_0_xboole_0,sK5,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8243,c_635])).

cnf(c_8365,plain,
    ( r2_hidden(sK7,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8363,c_9])).

cnf(c_8382,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8355,c_8365])).


%------------------------------------------------------------------------------
