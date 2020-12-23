%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:49 EST 2020

% Result     : Theorem 47.46s
% Output     : CNFRefutation 47.46s
% Verified   : 
% Statistics : Number of formulae       :  381 (7151 expanded)
%              Number of clauses        :  264 (1674 expanded)
%              Number of leaves         :   32 (2103 expanded)
%              Depth                    :   22
%              Number of atoms          : 1624 (80816 expanded)
%              Number of equality atoms :  684 (8802 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f74])).

fof(f110,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f75])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f81,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f82,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f81])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | v5_pre_topc(X2,X0,X1) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
          & v1_funct_1(X3) )
     => ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK6 = X2
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | v5_pre_topc(X2,X0,X1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ v5_pre_topc(sK5,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK5,X0,X1) )
            & sK5 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
                  | ~ v5_pre_topc(X2,X0,sK4) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
                  | v5_pre_topc(X2,X0,sK4) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK3,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,
    ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | ~ v5_pre_topc(sK5,sK3,sK4) )
    & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | v5_pre_topc(sK5,sK3,sK4) )
    & sK5 = sK6
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f82,f86,f85,f84,f83])).

fof(f147,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(cnf_transformation,[],[f87])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f145,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f87])).

fof(f146,plain,(
    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(cnf_transformation,[],[f87])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f70])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f151,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f95])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f43])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f156,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f134])).

fof(f140,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f87])).

fof(f141,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f87])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f58,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f133,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f131,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f132,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f144,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f87])).

fof(f148,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f87])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f103,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f143,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f87])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f158,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f136])).

fof(f138,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

fof(f139,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

fof(f149,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f87])).

fof(f150,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f87])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f157,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f137])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f155,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f135])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f129,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f152,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f94])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_448,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_449,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_448])).

cnf(c_554,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_449])).

cnf(c_93554,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6))
    | ~ r1_tarski(k2_relat_1(sK6),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_93568,plain,
    ( r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_93554])).

cnf(c_93570,plain,
    ( r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_93568])).

cnf(c_4259,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_45945,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != X0
    | u1_struct_0(sK3) != X0
    | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_4259])).

cnf(c_64305,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_relat_1(sK6)
    | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | u1_struct_0(sK3) != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_45945])).

cnf(c_24,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_63885,plain,
    ( r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6))
    | k1_xboole_0 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_63892,plain,
    ( k1_xboole_0 = k2_relat_1(sK6)
    | r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63885])).

cnf(c_53,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_5360,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_31,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_998,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_39,c_31])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1002,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_998,c_18,c_16])).

cnf(c_1003,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_1002])).

cnf(c_5346,plain,
    ( k1_relat_1(X0) = X1
    | k1_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1003])).

cnf(c_6191,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_5346])).

cnf(c_55,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_54,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_6195,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6191])).

cnf(c_6467,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6191,c_55,c_54,c_6195])).

cnf(c_6471,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6467,c_5360])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f151])).

cnf(c_6473,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6471,c_5])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_5380,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8235,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_5380])).

cnf(c_8780,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK6) = k1_relat_1(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_6473,c_8235])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_5381,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_56508,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8780,c_5381])).

cnf(c_56511,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_56508,c_5])).

cnf(c_56653,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(X0)) = iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_56511,c_6473])).

cnf(c_56654,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_56653])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_5385,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_56659,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_56654,c_5385])).

cnf(c_56831,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56659])).

cnf(c_48411,plain,
    ( X0 != X1
    | X0 = k1_relat_1(sK6)
    | k1_relat_1(sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_4259])).

cnf(c_48413,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_48411])).

cnf(c_4269,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_45243,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK5,X3,X4)
    | X3 != X1
    | X4 != X2
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_46614,plain,
    ( v1_funct_2(sK5,X0,X1)
    | ~ v1_funct_2(sK6,X2,X3)
    | X0 != X2
    | X1 != X3
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_45243])).

cnf(c_47555,plain,
    ( v1_funct_2(sK5,X0,X1)
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6))
    | X0 != k1_relat_1(sK6)
    | X1 != k2_relat_1(sK6)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_46614])).

cnf(c_47556,plain,
    ( X0 != k1_relat_1(sK6)
    | X1 != k2_relat_1(sK6)
    | sK5 != sK6
    | v1_funct_2(sK5,X0,X1) = iProver_top
    | v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47555])).

cnf(c_47558,plain,
    ( sK5 != sK6
    | k1_xboole_0 != k1_relat_1(sK6)
    | k1_xboole_0 != k2_relat_1(sK6)
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47556])).

cnf(c_45464,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK6,X3,X4)
    | X3 != X1
    | X4 != X2
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_46946,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | v1_funct_2(sK6,X2,X3)
    | X2 != X0
    | X3 != X1
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_45464])).

cnf(c_46947,plain,
    ( X0 != X1
    | X2 != X3
    | sK6 != sK5
    | v1_funct_2(sK5,X1,X3) != iProver_top
    | v1_funct_2(sK6,X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46946])).

cnf(c_46949,plain,
    ( sK6 != sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_46947])).

cnf(c_9007,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK6,X3,X4)
    | X3 != X1
    | X4 != X2
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_12992,plain,
    ( ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | v1_funct_2(sK6,X1,X2)
    | X1 != k1_relat_1(X0)
    | X2 != k2_relat_1(X0)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_9007])).

cnf(c_22296,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6))
    | X0 != k1_relat_1(sK6)
    | X1 != k2_relat_1(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_12992])).

cnf(c_28807,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0)
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6))
    | X0 != k2_relat_1(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_relat_1(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_22296])).

cnf(c_28808,plain,
    ( X0 != k2_relat_1(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_relat_1(sK6)
    | sK6 != sK6
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0) = iProver_top
    | v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28807])).

cnf(c_28810,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_relat_1(sK6)
    | sK6 != sK6
    | k1_xboole_0 != k2_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top
    | v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_28808])).

cnf(c_12654,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK4)
    | u1_struct_0(sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_4259])).

cnf(c_23979,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4)
    | u1_struct_0(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_12654])).

cnf(c_23980,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0
    | u1_struct_0(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23979])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_20904,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | k1_xboole_0 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_20170,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | k1_xboole_0 = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_5379,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10856,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_5379])).

cnf(c_47,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_5365,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_11256,plain,
    ( v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10856,c_5365])).

cnf(c_60,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_65,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_59,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_66,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_70,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_45,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_5534,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_5535,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5534])).

cnf(c_43,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_5612,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_5613,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5612])).

cnf(c_44,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_5789,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_5790,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5789])).

cnf(c_12305,plain,
    ( v2_pre_topc(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11256,c_65,c_66,c_70,c_5535,c_5613,c_5790])).

cnf(c_12306,plain,
    ( v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12305])).

cnf(c_12313,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6467,c_12306])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_190,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5684,plain,
    ( r2_hidden(sK1(sK6),sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_5688,plain,
    ( k1_xboole_0 = sK6
    | r2_hidden(sK1(sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5684])).

cnf(c_5719,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_4259])).

cnf(c_6204,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_5719])).

cnf(c_6205,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_6204])).

cnf(c_5359,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_6472,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6467,c_5359])).

cnf(c_4258,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6500,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_4258])).

cnf(c_6870,plain,
    ( ~ r2_hidden(sK1(sK6),sK6)
    | ~ r1_tarski(sK6,X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_6871,plain,
    ( r2_hidden(sK1(sK6),sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6870])).

cnf(c_6873,plain,
    ( r2_hidden(sK1(sK6),sK6) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6871])).

cnf(c_4262,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6876,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_4262])).

cnf(c_6878,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6876])).

cnf(c_7078,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_5385])).

cnf(c_56,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_5357,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_52,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f148])).

cnf(c_5395,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5357,c_52])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_15,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_15])).

cnf(c_349,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_348])).

cnf(c_5350,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_6945,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_5350])).

cnf(c_57,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_5356,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_5394,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5356,c_52])).

cnf(c_7235,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6945,c_5394])).

cnf(c_5388,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7241,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7235,c_5388])).

cnf(c_7357,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7241,c_5388])).

cnf(c_7359,plain,
    ( ~ v1_xboole_0(sK6)
    | u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7357])).

cnf(c_8232,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_5395,c_5380])).

cnf(c_8833,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8232,c_5381])).

cnf(c_9043,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8833,c_5395])).

cnf(c_9047,plain,
    ( r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9043,c_5385])).

cnf(c_8231,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_5360,c_5380])).

cnf(c_8832,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8231,c_5381])).

cnf(c_72,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_9169,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8832,c_72])).

cnf(c_9174,plain,
    ( r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9169,c_5385])).

cnf(c_6227,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != X1
    | u1_struct_0(sK4) != X2
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_7606,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != X0
    | u1_struct_0(sK4) != X1
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_6227])).

cnf(c_10381,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | u1_struct_0(sK4) != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_7606])).

cnf(c_10382,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | u1_struct_0(sK4) != X0
    | sK6 != sK6
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10381])).

cnf(c_10384,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | u1_struct_0(sK4) != k1_xboole_0
    | sK6 != sK6
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10382])).

cnf(c_10857,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK4)))) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_5379])).

cnf(c_49,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_5363,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_7426,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_5363])).

cnf(c_62,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_63,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_64,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_71,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_51,negated_conjecture,
    ( v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_5361,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_5396,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5361,c_52])).

cnf(c_50,negated_conjecture,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_5362,plain,
    ( v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_5397,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5362,c_52])).

cnf(c_5519,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_5520,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5519])).

cnf(c_5602,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_5603,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5602])).

cnf(c_5731,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_5732,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5731])).

cnf(c_48,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_5628,plain,
    ( ~ v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,X0,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_5871,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5628])).

cnf(c_5872,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5871])).

cnf(c_46,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_5627,plain,
    ( v5_pre_topc(sK6,X0,sK4)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_5894,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5627])).

cnf(c_5895,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5894])).

cnf(c_5859,plain,
    ( ~ v5_pre_topc(sK6,X0,sK4)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_6434,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5859])).

cnf(c_6435,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6434])).

cnf(c_7779,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7426,c_63,c_64,c_65,c_66,c_70,c_71,c_72,c_5396,c_5394,c_5395,c_5397,c_5520,c_5603,c_5732,c_5872,c_5895,c_6435])).

cnf(c_7780,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7779])).

cnf(c_7783,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7780,c_63,c_64,c_65,c_66,c_70,c_71,c_72,c_5396,c_5394,c_5395,c_5520,c_5603,c_5732,c_5872,c_6435])).

cnf(c_11135,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10857,c_7783])).

cnf(c_8731,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_5365])).

cnf(c_5868,plain,
    ( ~ v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5628])).

cnf(c_5869,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5868])).

cnf(c_5931,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_5935,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5931])).

cnf(c_5937,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_5938,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5937])).

cnf(c_8938,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8731,c_63,c_64,c_65,c_66,c_70,c_71,c_72,c_5396,c_5394,c_5395,c_5397,c_5535,c_5613,c_5790,c_5869,c_5935,c_5938])).

cnf(c_8939,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8938])).

cnf(c_8942,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8939,c_63,c_64,c_65,c_66,c_70,c_71,c_72,c_5396,c_5394,c_5395,c_5535,c_5613,c_5790,c_5935,c_5938])).

cnf(c_11260,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10856,c_8942])).

cnf(c_12153,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_4258])).

cnf(c_6061,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X2
    | u1_struct_0(sK3) != X1
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_7170,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X1
    | u1_struct_0(sK3) != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_6061])).

cnf(c_16350,plain,
    ( ~ v1_funct_2(sK6,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | u1_struct_0(sK3) != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_7170])).

cnf(c_16351,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | u1_struct_0(sK3) != X0
    | sK6 != sK6
    | v1_funct_2(sK6,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16350])).

cnf(c_16353,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | u1_struct_0(sK3) != k1_xboole_0
    | sK6 != sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
    | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16351])).

cnf(c_20034,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_4258])).

cnf(c_20057,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12313,c_3,c_190,c_5688,c_6205,c_6472,c_6500,c_6873,c_6878,c_7078,c_7359,c_9047,c_9174,c_10384,c_11135,c_11260,c_12153,c_16353,c_20034])).

cnf(c_20061,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6467,c_20057])).

cnf(c_12982,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | v1_funct_2(sK6,X0,X1)
    | X1 != u1_struct_0(sK4)
    | X0 != u1_struct_0(sK3)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_9007])).

cnf(c_19760,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | v1_funct_2(sK6,X0,u1_struct_0(sK4))
    | X0 != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_12982])).

cnf(c_19761,plain,
    ( X0 != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK6 != sK5
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,X0,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19760])).

cnf(c_19763,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK6 != sK5
    | k1_xboole_0 != u1_struct_0(sK3)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19761])).

cnf(c_8716,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK6,u1_struct_0(sK3),X3)
    | X3 != X2
    | u1_struct_0(sK3) != X1
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_15141,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v1_funct_2(sK6,u1_struct_0(sK3),X0)
    | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | u1_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_8716])).

cnf(c_19597,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | u1_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_15141])).

cnf(c_15146,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | v1_funct_2(sK6,u1_struct_0(sK3),X0)
    | X0 != u1_struct_0(sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_8716])).

cnf(c_15147,plain,
    ( X0 != u1_struct_0(sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK5
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15146])).

cnf(c_15149,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK5
    | k1_xboole_0 != u1_struct_0(sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_15147])).

cnf(c_6192,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_5346])).

cnf(c_6248,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6192,c_70,c_5394])).

cnf(c_5386,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7787,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5386,c_7783])).

cnf(c_7796,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6248,c_7787])).

cnf(c_7797,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7796,c_5])).

cnf(c_11658,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7797,c_9174,c_11135])).

cnf(c_11663,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6248,c_11658])).

cnf(c_11290,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11260])).

cnf(c_11130,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | k1_relat_1(sK6) = X0
    | v1_funct_2(sK6,X0,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10857,c_5346])).

cnf(c_11146,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | k1_relat_1(sK6) = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11130])).

cnf(c_8946,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5386,c_8942])).

cnf(c_9051,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6248,c_8946])).

cnf(c_9178,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6467,c_9051])).

cnf(c_8380,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4258])).

cnf(c_8947,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6467,c_8942])).

cnf(c_8949,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8947,c_5])).

cnf(c_10156,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),X0)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_7170])).

cnf(c_10157,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),X0) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10156])).

cnf(c_10159,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10157])).

cnf(c_10600,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9178,c_6467,c_6473,c_6500,c_8380,c_8949,c_10159])).

cnf(c_10601,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10600])).

cnf(c_7175,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X1
    | u1_struct_0(sK3) != X0
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_6061])).

cnf(c_8069,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),X0)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_7175])).

cnf(c_9784,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_8069])).

cnf(c_9785,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK5
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9784])).

cnf(c_9048,plain,
    ( r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9047])).

cnf(c_8356,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4258])).

cnf(c_5382,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7566,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_5382])).

cnf(c_6952,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6945])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_14,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_745,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_14])).

cnf(c_749,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_16])).

cnf(c_750,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_749])).

cnf(c_5348,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_6484,plain,
    ( r1_tarski(k2_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_5348])).

cnf(c_6672,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6467,c_6484])).

cnf(c_6485,plain,
    ( r1_tarski(k2_relat_1(sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_5348])).

cnf(c_6613,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6248,c_6485])).

cnf(c_5663,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_4259])).

cnf(c_5908,plain,
    ( X0 = sK5
    | X0 != sK6
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_5663])).

cnf(c_5959,plain,
    ( sK5 != sK6
    | sK6 = sK5
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_5908])).

cnf(c_5420,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5394])).

cnf(c_41,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2077,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_55])).

cnf(c_2078,plain,
    ( v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_2077])).

cnf(c_2079,plain,
    ( v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2078])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f152])).

cnf(c_186,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_185,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_68,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93570,c_64305,c_63892,c_56831,c_48413,c_47558,c_46949,c_28810,c_23980,c_20904,c_20170,c_20061,c_20034,c_19763,c_19597,c_15149,c_11663,c_11290,c_11260,c_11146,c_10601,c_9785,c_9048,c_9047,c_8380,c_8356,c_7566,c_7078,c_6952,c_6878,c_6873,c_6672,c_6613,c_6500,c_6467,c_6205,c_5959,c_5688,c_5420,c_2079,c_190,c_3,c_186,c_185,c_52,c_54,c_70,c_68])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:46:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 47.46/6.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.46/6.48  
% 47.46/6.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.46/6.48  
% 47.46/6.48  ------  iProver source info
% 47.46/6.48  
% 47.46/6.48  git: date: 2020-06-30 10:37:57 +0100
% 47.46/6.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.46/6.48  git: non_committed_changes: false
% 47.46/6.48  git: last_make_outside_of_git: false
% 47.46/6.48  
% 47.46/6.48  ------ 
% 47.46/6.48  
% 47.46/6.48  ------ Input Options
% 47.46/6.48  
% 47.46/6.48  --out_options                           all
% 47.46/6.48  --tptp_safe_out                         true
% 47.46/6.48  --problem_path                          ""
% 47.46/6.48  --include_path                          ""
% 47.46/6.48  --clausifier                            res/vclausify_rel
% 47.46/6.48  --clausifier_options                    ""
% 47.46/6.48  --stdin                                 false
% 47.46/6.48  --stats_out                             all
% 47.46/6.48  
% 47.46/6.48  ------ General Options
% 47.46/6.48  
% 47.46/6.48  --fof                                   false
% 47.46/6.48  --time_out_real                         305.
% 47.46/6.48  --time_out_virtual                      -1.
% 47.46/6.48  --symbol_type_check                     false
% 47.46/6.48  --clausify_out                          false
% 47.46/6.48  --sig_cnt_out                           false
% 47.46/6.48  --trig_cnt_out                          false
% 47.46/6.48  --trig_cnt_out_tolerance                1.
% 47.46/6.48  --trig_cnt_out_sk_spl                   false
% 47.46/6.48  --abstr_cl_out                          false
% 47.46/6.48  
% 47.46/6.48  ------ Global Options
% 47.46/6.48  
% 47.46/6.48  --schedule                              default
% 47.46/6.48  --add_important_lit                     false
% 47.46/6.48  --prop_solver_per_cl                    1000
% 47.46/6.48  --min_unsat_core                        false
% 47.46/6.48  --soft_assumptions                      false
% 47.46/6.48  --soft_lemma_size                       3
% 47.46/6.48  --prop_impl_unit_size                   0
% 47.46/6.48  --prop_impl_unit                        []
% 47.46/6.48  --share_sel_clauses                     true
% 47.46/6.48  --reset_solvers                         false
% 47.46/6.48  --bc_imp_inh                            [conj_cone]
% 47.46/6.48  --conj_cone_tolerance                   3.
% 47.46/6.48  --extra_neg_conj                        none
% 47.46/6.48  --large_theory_mode                     true
% 47.46/6.48  --prolific_symb_bound                   200
% 47.46/6.48  --lt_threshold                          2000
% 47.46/6.48  --clause_weak_htbl                      true
% 47.46/6.48  --gc_record_bc_elim                     false
% 47.46/6.48  
% 47.46/6.48  ------ Preprocessing Options
% 47.46/6.48  
% 47.46/6.48  --preprocessing_flag                    true
% 47.46/6.48  --time_out_prep_mult                    0.1
% 47.46/6.48  --splitting_mode                        input
% 47.46/6.48  --splitting_grd                         true
% 47.46/6.48  --splitting_cvd                         false
% 47.46/6.48  --splitting_cvd_svl                     false
% 47.46/6.48  --splitting_nvd                         32
% 47.46/6.48  --sub_typing                            true
% 47.46/6.48  --prep_gs_sim                           true
% 47.46/6.48  --prep_unflatten                        true
% 47.46/6.48  --prep_res_sim                          true
% 47.46/6.48  --prep_upred                            true
% 47.46/6.48  --prep_sem_filter                       exhaustive
% 47.46/6.48  --prep_sem_filter_out                   false
% 47.46/6.48  --pred_elim                             true
% 47.46/6.48  --res_sim_input                         true
% 47.46/6.48  --eq_ax_congr_red                       true
% 47.46/6.48  --pure_diseq_elim                       true
% 47.46/6.48  --brand_transform                       false
% 47.46/6.48  --non_eq_to_eq                          false
% 47.46/6.48  --prep_def_merge                        true
% 47.46/6.48  --prep_def_merge_prop_impl              false
% 47.46/6.48  --prep_def_merge_mbd                    true
% 47.46/6.48  --prep_def_merge_tr_red                 false
% 47.46/6.48  --prep_def_merge_tr_cl                  false
% 47.46/6.48  --smt_preprocessing                     true
% 47.46/6.48  --smt_ac_axioms                         fast
% 47.46/6.48  --preprocessed_out                      false
% 47.46/6.48  --preprocessed_stats                    false
% 47.46/6.48  
% 47.46/6.48  ------ Abstraction refinement Options
% 47.46/6.48  
% 47.46/6.48  --abstr_ref                             []
% 47.46/6.48  --abstr_ref_prep                        false
% 47.46/6.48  --abstr_ref_until_sat                   false
% 47.46/6.48  --abstr_ref_sig_restrict                funpre
% 47.46/6.48  --abstr_ref_af_restrict_to_split_sk     false
% 47.46/6.48  --abstr_ref_under                       []
% 47.46/6.48  
% 47.46/6.48  ------ SAT Options
% 47.46/6.48  
% 47.46/6.48  --sat_mode                              false
% 47.46/6.48  --sat_fm_restart_options                ""
% 47.46/6.48  --sat_gr_def                            false
% 47.46/6.48  --sat_epr_types                         true
% 47.46/6.48  --sat_non_cyclic_types                  false
% 47.46/6.48  --sat_finite_models                     false
% 47.46/6.48  --sat_fm_lemmas                         false
% 47.46/6.48  --sat_fm_prep                           false
% 47.46/6.48  --sat_fm_uc_incr                        true
% 47.46/6.48  --sat_out_model                         small
% 47.46/6.48  --sat_out_clauses                       false
% 47.46/6.48  
% 47.46/6.48  ------ QBF Options
% 47.46/6.48  
% 47.46/6.48  --qbf_mode                              false
% 47.46/6.48  --qbf_elim_univ                         false
% 47.46/6.48  --qbf_dom_inst                          none
% 47.46/6.48  --qbf_dom_pre_inst                      false
% 47.46/6.48  --qbf_sk_in                             false
% 47.46/6.48  --qbf_pred_elim                         true
% 47.46/6.48  --qbf_split                             512
% 47.46/6.48  
% 47.46/6.48  ------ BMC1 Options
% 47.46/6.48  
% 47.46/6.48  --bmc1_incremental                      false
% 47.46/6.48  --bmc1_axioms                           reachable_all
% 47.46/6.48  --bmc1_min_bound                        0
% 47.46/6.48  --bmc1_max_bound                        -1
% 47.46/6.48  --bmc1_max_bound_default                -1
% 47.46/6.48  --bmc1_symbol_reachability              true
% 47.46/6.48  --bmc1_property_lemmas                  false
% 47.46/6.48  --bmc1_k_induction                      false
% 47.46/6.48  --bmc1_non_equiv_states                 false
% 47.46/6.48  --bmc1_deadlock                         false
% 47.46/6.48  --bmc1_ucm                              false
% 47.46/6.48  --bmc1_add_unsat_core                   none
% 47.46/6.48  --bmc1_unsat_core_children              false
% 47.46/6.48  --bmc1_unsat_core_extrapolate_axioms    false
% 47.46/6.48  --bmc1_out_stat                         full
% 47.46/6.48  --bmc1_ground_init                      false
% 47.46/6.48  --bmc1_pre_inst_next_state              false
% 47.46/6.48  --bmc1_pre_inst_state                   false
% 47.46/6.48  --bmc1_pre_inst_reach_state             false
% 47.46/6.48  --bmc1_out_unsat_core                   false
% 47.46/6.48  --bmc1_aig_witness_out                  false
% 47.46/6.48  --bmc1_verbose                          false
% 47.46/6.48  --bmc1_dump_clauses_tptp                false
% 47.46/6.48  --bmc1_dump_unsat_core_tptp             false
% 47.46/6.48  --bmc1_dump_file                        -
% 47.46/6.48  --bmc1_ucm_expand_uc_limit              128
% 47.46/6.48  --bmc1_ucm_n_expand_iterations          6
% 47.46/6.48  --bmc1_ucm_extend_mode                  1
% 47.46/6.48  --bmc1_ucm_init_mode                    2
% 47.46/6.48  --bmc1_ucm_cone_mode                    none
% 47.46/6.48  --bmc1_ucm_reduced_relation_type        0
% 47.46/6.48  --bmc1_ucm_relax_model                  4
% 47.46/6.48  --bmc1_ucm_full_tr_after_sat            true
% 47.46/6.48  --bmc1_ucm_expand_neg_assumptions       false
% 47.46/6.48  --bmc1_ucm_layered_model                none
% 47.46/6.48  --bmc1_ucm_max_lemma_size               10
% 47.46/6.48  
% 47.46/6.48  ------ AIG Options
% 47.46/6.48  
% 47.46/6.48  --aig_mode                              false
% 47.46/6.48  
% 47.46/6.48  ------ Instantiation Options
% 47.46/6.48  
% 47.46/6.48  --instantiation_flag                    true
% 47.46/6.48  --inst_sos_flag                         true
% 47.46/6.48  --inst_sos_phase                        true
% 47.46/6.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.46/6.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.46/6.48  --inst_lit_sel_side                     num_symb
% 47.46/6.48  --inst_solver_per_active                1400
% 47.46/6.48  --inst_solver_calls_frac                1.
% 47.46/6.48  --inst_passive_queue_type               priority_queues
% 47.46/6.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.46/6.48  --inst_passive_queues_freq              [25;2]
% 47.46/6.48  --inst_dismatching                      true
% 47.46/6.48  --inst_eager_unprocessed_to_passive     true
% 47.46/6.48  --inst_prop_sim_given                   true
% 47.46/6.48  --inst_prop_sim_new                     false
% 47.46/6.48  --inst_subs_new                         false
% 47.46/6.48  --inst_eq_res_simp                      false
% 47.46/6.48  --inst_subs_given                       false
% 47.46/6.48  --inst_orphan_elimination               true
% 47.46/6.48  --inst_learning_loop_flag               true
% 47.46/6.48  --inst_learning_start                   3000
% 47.46/6.48  --inst_learning_factor                  2
% 47.46/6.48  --inst_start_prop_sim_after_learn       3
% 47.46/6.48  --inst_sel_renew                        solver
% 47.46/6.48  --inst_lit_activity_flag                true
% 47.46/6.48  --inst_restr_to_given                   false
% 47.46/6.48  --inst_activity_threshold               500
% 47.46/6.48  --inst_out_proof                        true
% 47.46/6.48  
% 47.46/6.48  ------ Resolution Options
% 47.46/6.48  
% 47.46/6.48  --resolution_flag                       true
% 47.46/6.48  --res_lit_sel                           adaptive
% 47.46/6.48  --res_lit_sel_side                      none
% 47.46/6.48  --res_ordering                          kbo
% 47.46/6.48  --res_to_prop_solver                    active
% 47.46/6.48  --res_prop_simpl_new                    false
% 47.46/6.48  --res_prop_simpl_given                  true
% 47.46/6.48  --res_passive_queue_type                priority_queues
% 47.46/6.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.46/6.48  --res_passive_queues_freq               [15;5]
% 47.46/6.48  --res_forward_subs                      full
% 47.46/6.48  --res_backward_subs                     full
% 47.46/6.48  --res_forward_subs_resolution           true
% 47.46/6.48  --res_backward_subs_resolution          true
% 47.46/6.48  --res_orphan_elimination                true
% 47.46/6.48  --res_time_limit                        2.
% 47.46/6.48  --res_out_proof                         true
% 47.46/6.48  
% 47.46/6.48  ------ Superposition Options
% 47.46/6.48  
% 47.46/6.48  --superposition_flag                    true
% 47.46/6.48  --sup_passive_queue_type                priority_queues
% 47.46/6.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.46/6.48  --sup_passive_queues_freq               [8;1;4]
% 47.46/6.48  --demod_completeness_check              fast
% 47.46/6.48  --demod_use_ground                      true
% 47.46/6.48  --sup_to_prop_solver                    passive
% 47.46/6.48  --sup_prop_simpl_new                    true
% 47.46/6.48  --sup_prop_simpl_given                  true
% 47.46/6.48  --sup_fun_splitting                     true
% 47.46/6.48  --sup_smt_interval                      50000
% 47.46/6.48  
% 47.46/6.48  ------ Superposition Simplification Setup
% 47.46/6.48  
% 47.46/6.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.46/6.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.46/6.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.46/6.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.46/6.48  --sup_full_triv                         [TrivRules;PropSubs]
% 47.46/6.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.46/6.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.46/6.48  --sup_immed_triv                        [TrivRules]
% 47.46/6.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.46/6.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.46/6.48  --sup_immed_bw_main                     []
% 47.46/6.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.46/6.48  --sup_input_triv                        [Unflattening;TrivRules]
% 47.46/6.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.46/6.48  --sup_input_bw                          []
% 47.46/6.48  
% 47.46/6.48  ------ Combination Options
% 47.46/6.48  
% 47.46/6.48  --comb_res_mult                         3
% 47.46/6.48  --comb_sup_mult                         2
% 47.46/6.48  --comb_inst_mult                        10
% 47.46/6.48  
% 47.46/6.48  ------ Debug Options
% 47.46/6.48  
% 47.46/6.48  --dbg_backtrace                         false
% 47.46/6.48  --dbg_dump_prop_clauses                 false
% 47.46/6.48  --dbg_dump_prop_clauses_file            -
% 47.46/6.48  --dbg_out_stat                          false
% 47.46/6.48  ------ Parsing...
% 47.46/6.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.46/6.48  
% 47.46/6.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 47.46/6.48  
% 47.46/6.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.46/6.48  
% 47.46/6.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.48  ------ Proving...
% 47.46/6.48  ------ Problem Properties 
% 47.46/6.48  
% 47.46/6.48  
% 47.46/6.48  clauses                                 53
% 47.46/6.48  conjectures                             13
% 47.46/6.48  EPR                                     12
% 47.46/6.48  Horn                                    46
% 47.46/6.48  unary                                   20
% 47.46/6.48  binary                                  15
% 47.46/6.48  lits                                    143
% 47.46/6.48  lits eq                                 17
% 47.46/6.48  fd_pure                                 0
% 47.46/6.48  fd_pseudo                               0
% 47.46/6.48  fd_cond                                 5
% 47.46/6.48  fd_pseudo_cond                          2
% 47.46/6.48  AC symbols                              0
% 47.46/6.48  
% 47.46/6.48  ------ Schedule dynamic 5 is on 
% 47.46/6.48  
% 47.46/6.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.46/6.48  
% 47.46/6.48  
% 47.46/6.48  ------ 
% 47.46/6.48  Current options:
% 47.46/6.48  ------ 
% 47.46/6.48  
% 47.46/6.48  ------ Input Options
% 47.46/6.48  
% 47.46/6.48  --out_options                           all
% 47.46/6.48  --tptp_safe_out                         true
% 47.46/6.48  --problem_path                          ""
% 47.46/6.48  --include_path                          ""
% 47.46/6.48  --clausifier                            res/vclausify_rel
% 47.46/6.48  --clausifier_options                    ""
% 47.46/6.48  --stdin                                 false
% 47.46/6.48  --stats_out                             all
% 47.46/6.48  
% 47.46/6.48  ------ General Options
% 47.46/6.48  
% 47.46/6.48  --fof                                   false
% 47.46/6.48  --time_out_real                         305.
% 47.46/6.48  --time_out_virtual                      -1.
% 47.46/6.48  --symbol_type_check                     false
% 47.46/6.48  --clausify_out                          false
% 47.46/6.48  --sig_cnt_out                           false
% 47.46/6.48  --trig_cnt_out                          false
% 47.46/6.48  --trig_cnt_out_tolerance                1.
% 47.46/6.48  --trig_cnt_out_sk_spl                   false
% 47.46/6.48  --abstr_cl_out                          false
% 47.46/6.48  
% 47.46/6.48  ------ Global Options
% 47.46/6.48  
% 47.46/6.48  --schedule                              default
% 47.46/6.48  --add_important_lit                     false
% 47.46/6.48  --prop_solver_per_cl                    1000
% 47.46/6.48  --min_unsat_core                        false
% 47.46/6.48  --soft_assumptions                      false
% 47.46/6.48  --soft_lemma_size                       3
% 47.46/6.48  --prop_impl_unit_size                   0
% 47.46/6.48  --prop_impl_unit                        []
% 47.46/6.48  --share_sel_clauses                     true
% 47.46/6.48  --reset_solvers                         false
% 47.46/6.48  --bc_imp_inh                            [conj_cone]
% 47.46/6.48  --conj_cone_tolerance                   3.
% 47.46/6.48  --extra_neg_conj                        none
% 47.46/6.48  --large_theory_mode                     true
% 47.46/6.48  --prolific_symb_bound                   200
% 47.46/6.48  --lt_threshold                          2000
% 47.46/6.48  --clause_weak_htbl                      true
% 47.46/6.48  --gc_record_bc_elim                     false
% 47.46/6.48  
% 47.46/6.48  ------ Preprocessing Options
% 47.46/6.48  
% 47.46/6.48  --preprocessing_flag                    true
% 47.46/6.48  --time_out_prep_mult                    0.1
% 47.46/6.48  --splitting_mode                        input
% 47.46/6.48  --splitting_grd                         true
% 47.46/6.48  --splitting_cvd                         false
% 47.46/6.48  --splitting_cvd_svl                     false
% 47.46/6.48  --splitting_nvd                         32
% 47.46/6.48  --sub_typing                            true
% 47.46/6.48  --prep_gs_sim                           true
% 47.46/6.48  --prep_unflatten                        true
% 47.46/6.48  --prep_res_sim                          true
% 47.46/6.48  --prep_upred                            true
% 47.46/6.48  --prep_sem_filter                       exhaustive
% 47.46/6.48  --prep_sem_filter_out                   false
% 47.46/6.48  --pred_elim                             true
% 47.46/6.48  --res_sim_input                         true
% 47.46/6.48  --eq_ax_congr_red                       true
% 47.46/6.48  --pure_diseq_elim                       true
% 47.46/6.48  --brand_transform                       false
% 47.46/6.48  --non_eq_to_eq                          false
% 47.46/6.48  --prep_def_merge                        true
% 47.46/6.48  --prep_def_merge_prop_impl              false
% 47.46/6.48  --prep_def_merge_mbd                    true
% 47.46/6.48  --prep_def_merge_tr_red                 false
% 47.46/6.48  --prep_def_merge_tr_cl                  false
% 47.46/6.48  --smt_preprocessing                     true
% 47.46/6.48  --smt_ac_axioms                         fast
% 47.46/6.48  --preprocessed_out                      false
% 47.46/6.48  --preprocessed_stats                    false
% 47.46/6.48  
% 47.46/6.48  ------ Abstraction refinement Options
% 47.46/6.48  
% 47.46/6.48  --abstr_ref                             []
% 47.46/6.48  --abstr_ref_prep                        false
% 47.46/6.48  --abstr_ref_until_sat                   false
% 47.46/6.48  --abstr_ref_sig_restrict                funpre
% 47.46/6.48  --abstr_ref_af_restrict_to_split_sk     false
% 47.46/6.48  --abstr_ref_under                       []
% 47.46/6.48  
% 47.46/6.48  ------ SAT Options
% 47.46/6.48  
% 47.46/6.48  --sat_mode                              false
% 47.46/6.48  --sat_fm_restart_options                ""
% 47.46/6.48  --sat_gr_def                            false
% 47.46/6.48  --sat_epr_types                         true
% 47.46/6.48  --sat_non_cyclic_types                  false
% 47.46/6.48  --sat_finite_models                     false
% 47.46/6.48  --sat_fm_lemmas                         false
% 47.46/6.48  --sat_fm_prep                           false
% 47.46/6.48  --sat_fm_uc_incr                        true
% 47.46/6.48  --sat_out_model                         small
% 47.46/6.48  --sat_out_clauses                       false
% 47.46/6.48  
% 47.46/6.48  ------ QBF Options
% 47.46/6.48  
% 47.46/6.48  --qbf_mode                              false
% 47.46/6.48  --qbf_elim_univ                         false
% 47.46/6.48  --qbf_dom_inst                          none
% 47.46/6.48  --qbf_dom_pre_inst                      false
% 47.46/6.48  --qbf_sk_in                             false
% 47.46/6.48  --qbf_pred_elim                         true
% 47.46/6.48  --qbf_split                             512
% 47.46/6.48  
% 47.46/6.48  ------ BMC1 Options
% 47.46/6.48  
% 47.46/6.48  --bmc1_incremental                      false
% 47.46/6.48  --bmc1_axioms                           reachable_all
% 47.46/6.48  --bmc1_min_bound                        0
% 47.46/6.48  --bmc1_max_bound                        -1
% 47.46/6.48  --bmc1_max_bound_default                -1
% 47.46/6.48  --bmc1_symbol_reachability              true
% 47.46/6.48  --bmc1_property_lemmas                  false
% 47.46/6.48  --bmc1_k_induction                      false
% 47.46/6.48  --bmc1_non_equiv_states                 false
% 47.46/6.48  --bmc1_deadlock                         false
% 47.46/6.48  --bmc1_ucm                              false
% 47.46/6.48  --bmc1_add_unsat_core                   none
% 47.46/6.48  --bmc1_unsat_core_children              false
% 47.46/6.48  --bmc1_unsat_core_extrapolate_axioms    false
% 47.46/6.48  --bmc1_out_stat                         full
% 47.46/6.48  --bmc1_ground_init                      false
% 47.46/6.48  --bmc1_pre_inst_next_state              false
% 47.46/6.48  --bmc1_pre_inst_state                   false
% 47.46/6.48  --bmc1_pre_inst_reach_state             false
% 47.46/6.48  --bmc1_out_unsat_core                   false
% 47.46/6.48  --bmc1_aig_witness_out                  false
% 47.46/6.48  --bmc1_verbose                          false
% 47.46/6.48  --bmc1_dump_clauses_tptp                false
% 47.46/6.48  --bmc1_dump_unsat_core_tptp             false
% 47.46/6.48  --bmc1_dump_file                        -
% 47.46/6.48  --bmc1_ucm_expand_uc_limit              128
% 47.46/6.48  --bmc1_ucm_n_expand_iterations          6
% 47.46/6.48  --bmc1_ucm_extend_mode                  1
% 47.46/6.48  --bmc1_ucm_init_mode                    2
% 47.46/6.48  --bmc1_ucm_cone_mode                    none
% 47.46/6.48  --bmc1_ucm_reduced_relation_type        0
% 47.46/6.48  --bmc1_ucm_relax_model                  4
% 47.46/6.48  --bmc1_ucm_full_tr_after_sat            true
% 47.46/6.48  --bmc1_ucm_expand_neg_assumptions       false
% 47.46/6.48  --bmc1_ucm_layered_model                none
% 47.46/6.48  --bmc1_ucm_max_lemma_size               10
% 47.46/6.48  
% 47.46/6.48  ------ AIG Options
% 47.46/6.48  
% 47.46/6.48  --aig_mode                              false
% 47.46/6.48  
% 47.46/6.48  ------ Instantiation Options
% 47.46/6.48  
% 47.46/6.48  --instantiation_flag                    true
% 47.46/6.48  --inst_sos_flag                         true
% 47.46/6.48  --inst_sos_phase                        true
% 47.46/6.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.46/6.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.46/6.48  --inst_lit_sel_side                     none
% 47.46/6.48  --inst_solver_per_active                1400
% 47.46/6.48  --inst_solver_calls_frac                1.
% 47.46/6.48  --inst_passive_queue_type               priority_queues
% 47.46/6.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.46/6.48  --inst_passive_queues_freq              [25;2]
% 47.46/6.48  --inst_dismatching                      true
% 47.46/6.48  --inst_eager_unprocessed_to_passive     true
% 47.46/6.48  --inst_prop_sim_given                   true
% 47.46/6.48  --inst_prop_sim_new                     false
% 47.46/6.48  --inst_subs_new                         false
% 47.46/6.48  --inst_eq_res_simp                      false
% 47.46/6.48  --inst_subs_given                       false
% 47.46/6.48  --inst_orphan_elimination               true
% 47.46/6.48  --inst_learning_loop_flag               true
% 47.46/6.48  --inst_learning_start                   3000
% 47.46/6.48  --inst_learning_factor                  2
% 47.46/6.48  --inst_start_prop_sim_after_learn       3
% 47.46/6.48  --inst_sel_renew                        solver
% 47.46/6.48  --inst_lit_activity_flag                true
% 47.46/6.48  --inst_restr_to_given                   false
% 47.46/6.48  --inst_activity_threshold               500
% 47.46/6.48  --inst_out_proof                        true
% 47.46/6.48  
% 47.46/6.48  ------ Resolution Options
% 47.46/6.48  
% 47.46/6.48  --resolution_flag                       false
% 47.46/6.48  --res_lit_sel                           adaptive
% 47.46/6.48  --res_lit_sel_side                      none
% 47.46/6.48  --res_ordering                          kbo
% 47.46/6.48  --res_to_prop_solver                    active
% 47.46/6.48  --res_prop_simpl_new                    false
% 47.46/6.48  --res_prop_simpl_given                  true
% 47.46/6.48  --res_passive_queue_type                priority_queues
% 47.46/6.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.46/6.48  --res_passive_queues_freq               [15;5]
% 47.46/6.48  --res_forward_subs                      full
% 47.46/6.48  --res_backward_subs                     full
% 47.46/6.48  --res_forward_subs_resolution           true
% 47.46/6.48  --res_backward_subs_resolution          true
% 47.46/6.48  --res_orphan_elimination                true
% 47.46/6.48  --res_time_limit                        2.
% 47.46/6.48  --res_out_proof                         true
% 47.46/6.48  
% 47.46/6.48  ------ Superposition Options
% 47.46/6.48  
% 47.46/6.48  --superposition_flag                    true
% 47.46/6.48  --sup_passive_queue_type                priority_queues
% 47.46/6.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.46/6.48  --sup_passive_queues_freq               [8;1;4]
% 47.46/6.48  --demod_completeness_check              fast
% 47.46/6.48  --demod_use_ground                      true
% 47.46/6.48  --sup_to_prop_solver                    passive
% 47.46/6.48  --sup_prop_simpl_new                    true
% 47.46/6.48  --sup_prop_simpl_given                  true
% 47.46/6.48  --sup_fun_splitting                     true
% 47.46/6.48  --sup_smt_interval                      50000
% 47.46/6.48  
% 47.46/6.48  ------ Superposition Simplification Setup
% 47.46/6.48  
% 47.46/6.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.46/6.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.46/6.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.46/6.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.46/6.48  --sup_full_triv                         [TrivRules;PropSubs]
% 47.46/6.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.46/6.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.46/6.48  --sup_immed_triv                        [TrivRules]
% 47.46/6.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.46/6.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.46/6.48  --sup_immed_bw_main                     []
% 47.46/6.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.46/6.48  --sup_input_triv                        [Unflattening;TrivRules]
% 47.46/6.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.46/6.48  --sup_input_bw                          []
% 47.46/6.48  
% 47.46/6.48  ------ Combination Options
% 47.46/6.48  
% 47.46/6.48  --comb_res_mult                         3
% 47.46/6.48  --comb_sup_mult                         2
% 47.46/6.48  --comb_inst_mult                        10
% 47.46/6.48  
% 47.46/6.48  ------ Debug Options
% 47.46/6.48  
% 47.46/6.48  --dbg_backtrace                         false
% 47.46/6.48  --dbg_dump_prop_clauses                 false
% 47.46/6.48  --dbg_dump_prop_clauses_file            -
% 47.46/6.48  --dbg_out_stat                          false
% 47.46/6.48  
% 47.46/6.48  
% 47.46/6.48  
% 47.46/6.48  
% 47.46/6.48  ------ Proving...
% 47.46/6.48  
% 47.46/6.48  
% 47.46/6.48  % SZS status Theorem for theBenchmark.p
% 47.46/6.48  
% 47.46/6.48  % SZS output start CNFRefutation for theBenchmark.p
% 47.46/6.48  
% 47.46/6.48  fof(f8,axiom,(
% 47.46/6.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f36,plain,(
% 47.46/6.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 47.46/6.48    inference(ennf_transformation,[],[f8])).
% 47.46/6.48  
% 47.46/6.48  fof(f100,plain,(
% 47.46/6.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f36])).
% 47.46/6.48  
% 47.46/6.48  fof(f6,axiom,(
% 47.46/6.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f72,plain,(
% 47.46/6.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 47.46/6.48    inference(nnf_transformation,[],[f6])).
% 47.46/6.48  
% 47.46/6.48  fof(f98,plain,(
% 47.46/6.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f72])).
% 47.46/6.48  
% 47.46/6.48  fof(f16,axiom,(
% 47.46/6.48    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f45,plain,(
% 47.46/6.48    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 47.46/6.48    inference(ennf_transformation,[],[f16])).
% 47.46/6.48  
% 47.46/6.48  fof(f74,plain,(
% 47.46/6.48    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 47.46/6.48    introduced(choice_axiom,[])).
% 47.46/6.48  
% 47.46/6.48  fof(f75,plain,(
% 47.46/6.48    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 47.46/6.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f74])).
% 47.46/6.48  
% 47.46/6.48  fof(f110,plain,(
% 47.46/6.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 47.46/6.48    inference(cnf_transformation,[],[f75])).
% 47.46/6.48  
% 47.46/6.48  fof(f28,conjecture,(
% 47.46/6.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f29,negated_conjecture,(
% 47.46/6.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 47.46/6.48    inference(negated_conjecture,[],[f28])).
% 47.46/6.48  
% 47.46/6.48  fof(f64,plain,(
% 47.46/6.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 47.46/6.48    inference(ennf_transformation,[],[f29])).
% 47.46/6.48  
% 47.46/6.48  fof(f65,plain,(
% 47.46/6.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 47.46/6.48    inference(flattening,[],[f64])).
% 47.46/6.48  
% 47.46/6.48  fof(f81,plain,(
% 47.46/6.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 47.46/6.48    inference(nnf_transformation,[],[f65])).
% 47.46/6.48  
% 47.46/6.48  fof(f82,plain,(
% 47.46/6.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 47.46/6.48    inference(flattening,[],[f81])).
% 47.46/6.48  
% 47.46/6.48  fof(f86,plain,(
% 47.46/6.48    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK6 = X2 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK6))) )),
% 47.46/6.48    introduced(choice_axiom,[])).
% 47.46/6.48  
% 47.46/6.48  fof(f85,plain,(
% 47.46/6.48    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK5,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK5,X0,X1)) & sK5 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 47.46/6.48    introduced(choice_axiom,[])).
% 47.46/6.48  
% 47.46/6.48  fof(f84,plain,(
% 47.46/6.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(X2,X0,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(X2,X0,sK4)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))) )),
% 47.46/6.48    introduced(choice_axiom,[])).
% 47.46/6.48  
% 47.46/6.48  fof(f83,plain,(
% 47.46/6.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK3,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 47.46/6.48    introduced(choice_axiom,[])).
% 47.46/6.48  
% 47.46/6.48  fof(f87,plain,(
% 47.46/6.48    ((((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = sK6 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 47.46/6.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f82,f86,f85,f84,f83])).
% 47.46/6.48  
% 47.46/6.48  fof(f147,plain,(
% 47.46/6.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f21,axiom,(
% 47.46/6.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f52,plain,(
% 47.46/6.48    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 47.46/6.48    inference(ennf_transformation,[],[f21])).
% 47.46/6.48  
% 47.46/6.48  fof(f53,plain,(
% 47.46/6.48    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 47.46/6.48    inference(flattening,[],[f52])).
% 47.46/6.48  
% 47.46/6.48  fof(f126,plain,(
% 47.46/6.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f53])).
% 47.46/6.48  
% 47.46/6.48  fof(f19,axiom,(
% 47.46/6.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f50,plain,(
% 47.46/6.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 47.46/6.48    inference(ennf_transformation,[],[f19])).
% 47.46/6.48  
% 47.46/6.48  fof(f51,plain,(
% 47.46/6.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 47.46/6.48    inference(flattening,[],[f50])).
% 47.46/6.48  
% 47.46/6.48  fof(f76,plain,(
% 47.46/6.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 47.46/6.48    inference(nnf_transformation,[],[f51])).
% 47.46/6.48  
% 47.46/6.48  fof(f118,plain,(
% 47.46/6.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f76])).
% 47.46/6.48  
% 47.46/6.48  fof(f12,axiom,(
% 47.46/6.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f40,plain,(
% 47.46/6.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.48    inference(ennf_transformation,[],[f12])).
% 47.46/6.48  
% 47.46/6.48  fof(f105,plain,(
% 47.46/6.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.48    inference(cnf_transformation,[],[f40])).
% 47.46/6.48  
% 47.46/6.48  fof(f11,axiom,(
% 47.46/6.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f39,plain,(
% 47.46/6.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.48    inference(ennf_transformation,[],[f11])).
% 47.46/6.48  
% 47.46/6.48  fof(f104,plain,(
% 47.46/6.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.48    inference(cnf_transformation,[],[f39])).
% 47.46/6.48  
% 47.46/6.48  fof(f145,plain,(
% 47.46/6.48    v1_funct_1(sK6)),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f146,plain,(
% 47.46/6.48    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f4,axiom,(
% 47.46/6.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f70,plain,(
% 47.46/6.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 47.46/6.48    inference(nnf_transformation,[],[f4])).
% 47.46/6.48  
% 47.46/6.48  fof(f71,plain,(
% 47.46/6.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 47.46/6.48    inference(flattening,[],[f70])).
% 47.46/6.48  
% 47.46/6.48  fof(f95,plain,(
% 47.46/6.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 47.46/6.48    inference(cnf_transformation,[],[f71])).
% 47.46/6.48  
% 47.46/6.48  fof(f151,plain,(
% 47.46/6.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 47.46/6.48    inference(equality_resolution,[],[f95])).
% 47.46/6.48  
% 47.46/6.48  fof(f14,axiom,(
% 47.46/6.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f42,plain,(
% 47.46/6.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.48    inference(ennf_transformation,[],[f14])).
% 47.46/6.48  
% 47.46/6.48  fof(f108,plain,(
% 47.46/6.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.48    inference(cnf_transformation,[],[f42])).
% 47.46/6.48  
% 47.46/6.48  fof(f13,axiom,(
% 47.46/6.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f41,plain,(
% 47.46/6.48    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.48    inference(ennf_transformation,[],[f13])).
% 47.46/6.48  
% 47.46/6.48  fof(f107,plain,(
% 47.46/6.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.48    inference(cnf_transformation,[],[f41])).
% 47.46/6.48  
% 47.46/6.48  fof(f97,plain,(
% 47.46/6.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 47.46/6.48    inference(cnf_transformation,[],[f72])).
% 47.46/6.48  
% 47.46/6.48  fof(f3,axiom,(
% 47.46/6.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f33,plain,(
% 47.46/6.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 47.46/6.48    inference(ennf_transformation,[],[f3])).
% 47.46/6.48  
% 47.46/6.48  fof(f92,plain,(
% 47.46/6.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f33])).
% 47.46/6.48  
% 47.46/6.48  fof(f15,axiom,(
% 47.46/6.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f43,plain,(
% 47.46/6.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 47.46/6.48    inference(ennf_transformation,[],[f15])).
% 47.46/6.48  
% 47.46/6.48  fof(f44,plain,(
% 47.46/6.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 47.46/6.48    inference(flattening,[],[f43])).
% 47.46/6.48  
% 47.46/6.48  fof(f109,plain,(
% 47.46/6.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 47.46/6.48    inference(cnf_transformation,[],[f44])).
% 47.46/6.48  
% 47.46/6.48  fof(f26,axiom,(
% 47.46/6.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f60,plain,(
% 47.46/6.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 47.46/6.48    inference(ennf_transformation,[],[f26])).
% 47.46/6.48  
% 47.46/6.48  fof(f61,plain,(
% 47.46/6.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 47.46/6.48    inference(flattening,[],[f60])).
% 47.46/6.48  
% 47.46/6.48  fof(f79,plain,(
% 47.46/6.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 47.46/6.48    inference(nnf_transformation,[],[f61])).
% 47.46/6.48  
% 47.46/6.48  fof(f134,plain,(
% 47.46/6.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f79])).
% 47.46/6.48  
% 47.46/6.48  fof(f156,plain,(
% 47.46/6.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.46/6.48    inference(equality_resolution,[],[f134])).
% 47.46/6.48  
% 47.46/6.48  fof(f140,plain,(
% 47.46/6.48    v2_pre_topc(sK4)),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f141,plain,(
% 47.46/6.48    l1_pre_topc(sK4)),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f25,axiom,(
% 47.46/6.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f31,plain,(
% 47.46/6.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 47.46/6.48    inference(pure_predicate_removal,[],[f25])).
% 47.46/6.48  
% 47.46/6.48  fof(f58,plain,(
% 47.46/6.48    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 47.46/6.48    inference(ennf_transformation,[],[f31])).
% 47.46/6.48  
% 47.46/6.48  fof(f59,plain,(
% 47.46/6.48    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 47.46/6.48    inference(flattening,[],[f58])).
% 47.46/6.48  
% 47.46/6.48  fof(f133,plain,(
% 47.46/6.48    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f59])).
% 47.46/6.48  
% 47.46/6.48  fof(f23,axiom,(
% 47.46/6.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f30,plain,(
% 47.46/6.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 47.46/6.48    inference(pure_predicate_removal,[],[f23])).
% 47.46/6.48  
% 47.46/6.48  fof(f56,plain,(
% 47.46/6.48    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 47.46/6.48    inference(ennf_transformation,[],[f30])).
% 47.46/6.48  
% 47.46/6.48  fof(f131,plain,(
% 47.46/6.48    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 47.46/6.48    inference(cnf_transformation,[],[f56])).
% 47.46/6.48  
% 47.46/6.48  fof(f24,axiom,(
% 47.46/6.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f57,plain,(
% 47.46/6.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.46/6.48    inference(ennf_transformation,[],[f24])).
% 47.46/6.48  
% 47.46/6.48  fof(f132,plain,(
% 47.46/6.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f57])).
% 47.46/6.48  
% 47.46/6.48  fof(f2,axiom,(
% 47.46/6.48    v1_xboole_0(k1_xboole_0)),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f91,plain,(
% 47.46/6.48    v1_xboole_0(k1_xboole_0)),
% 47.46/6.48    inference(cnf_transformation,[],[f2])).
% 47.46/6.48  
% 47.46/6.48  fof(f144,plain,(
% 47.46/6.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f148,plain,(
% 47.46/6.48    sK5 = sK6),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f18,axiom,(
% 47.46/6.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f48,plain,(
% 47.46/6.48    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 47.46/6.48    inference(ennf_transformation,[],[f18])).
% 47.46/6.48  
% 47.46/6.48  fof(f49,plain,(
% 47.46/6.48    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 47.46/6.48    inference(flattening,[],[f48])).
% 47.46/6.48  
% 47.46/6.48  fof(f116,plain,(
% 47.46/6.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f49])).
% 47.46/6.48  
% 47.46/6.48  fof(f10,axiom,(
% 47.46/6.48    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f38,plain,(
% 47.46/6.48    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 47.46/6.48    inference(ennf_transformation,[],[f10])).
% 47.46/6.48  
% 47.46/6.48  fof(f103,plain,(
% 47.46/6.48    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f38])).
% 47.46/6.48  
% 47.46/6.48  fof(f143,plain,(
% 47.46/6.48    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f27,axiom,(
% 47.46/6.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f62,plain,(
% 47.46/6.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 47.46/6.48    inference(ennf_transformation,[],[f27])).
% 47.46/6.48  
% 47.46/6.48  fof(f63,plain,(
% 47.46/6.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 47.46/6.48    inference(flattening,[],[f62])).
% 47.46/6.48  
% 47.46/6.48  fof(f80,plain,(
% 47.46/6.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 47.46/6.48    inference(nnf_transformation,[],[f63])).
% 47.46/6.48  
% 47.46/6.48  fof(f136,plain,(
% 47.46/6.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f80])).
% 47.46/6.48  
% 47.46/6.48  fof(f158,plain,(
% 47.46/6.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.46/6.48    inference(equality_resolution,[],[f136])).
% 47.46/6.48  
% 47.46/6.48  fof(f138,plain,(
% 47.46/6.48    v2_pre_topc(sK3)),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f139,plain,(
% 47.46/6.48    l1_pre_topc(sK3)),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f149,plain,(
% 47.46/6.48    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f150,plain,(
% 47.46/6.48    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)),
% 47.46/6.48    inference(cnf_transformation,[],[f87])).
% 47.46/6.48  
% 47.46/6.48  fof(f137,plain,(
% 47.46/6.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f80])).
% 47.46/6.48  
% 47.46/6.48  fof(f157,plain,(
% 47.46/6.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.46/6.48    inference(equality_resolution,[],[f137])).
% 47.46/6.48  
% 47.46/6.48  fof(f135,plain,(
% 47.46/6.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f79])).
% 47.46/6.48  
% 47.46/6.48  fof(f155,plain,(
% 47.46/6.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.46/6.48    inference(equality_resolution,[],[f135])).
% 47.46/6.48  
% 47.46/6.48  fof(f106,plain,(
% 47.46/6.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.48    inference(cnf_transformation,[],[f40])).
% 47.46/6.48  
% 47.46/6.48  fof(f9,axiom,(
% 47.46/6.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f37,plain,(
% 47.46/6.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 47.46/6.48    inference(ennf_transformation,[],[f9])).
% 47.46/6.48  
% 47.46/6.48  fof(f73,plain,(
% 47.46/6.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 47.46/6.48    inference(nnf_transformation,[],[f37])).
% 47.46/6.48  
% 47.46/6.48  fof(f101,plain,(
% 47.46/6.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f73])).
% 47.46/6.48  
% 47.46/6.48  fof(f22,axiom,(
% 47.46/6.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 47.46/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.48  
% 47.46/6.48  fof(f54,plain,(
% 47.46/6.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 47.46/6.48    inference(ennf_transformation,[],[f22])).
% 47.46/6.48  
% 47.46/6.48  fof(f55,plain,(
% 47.46/6.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 47.46/6.48    inference(flattening,[],[f54])).
% 47.46/6.48  
% 47.46/6.48  fof(f129,plain,(
% 47.46/6.48    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f55])).
% 47.46/6.48  
% 47.46/6.48  fof(f94,plain,(
% 47.46/6.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 47.46/6.48    inference(cnf_transformation,[],[f71])).
% 47.46/6.48  
% 47.46/6.48  fof(f152,plain,(
% 47.46/6.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 47.46/6.48    inference(equality_resolution,[],[f94])).
% 47.46/6.48  
% 47.46/6.48  fof(f93,plain,(
% 47.46/6.48    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 47.46/6.48    inference(cnf_transformation,[],[f71])).
% 47.46/6.48  
% 47.46/6.48  cnf(c_12,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.46/6.48      | ~ r2_hidden(X2,X0)
% 47.46/6.48      | ~ v1_xboole_0(X1) ),
% 47.46/6.48      inference(cnf_transformation,[],[f100]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9,plain,
% 47.46/6.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.46/6.48      inference(cnf_transformation,[],[f98]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_448,plain,
% 47.46/6.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 47.46/6.48      inference(prop_impl,[status(thm)],[c_9]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_449,plain,
% 47.46/6.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.46/6.48      inference(renaming,[status(thm)],[c_448]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_554,plain,
% 47.46/6.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 47.46/6.48      inference(bin_hyper_res,[status(thm)],[c_12,c_449]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_93554,plain,
% 47.46/6.48      ( ~ r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6))
% 47.46/6.48      | ~ r1_tarski(k2_relat_1(sK6),X0)
% 47.46/6.48      | ~ v1_xboole_0(X0) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_554]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_93568,plain,
% 47.46/6.48      ( r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top
% 47.46/6.48      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top
% 47.46/6.48      | v1_xboole_0(X0) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_93554]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_93570,plain,
% 47.46/6.48      ( r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top
% 47.46/6.48      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
% 47.46/6.48      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_93568]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_4259,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_45945,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != X0
% 47.46/6.48      | u1_struct_0(sK3) != X0
% 47.46/6.48      | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4259]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_64305,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_relat_1(sK6)
% 47.46/6.48      | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 47.46/6.48      | u1_struct_0(sK3) != k1_relat_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_45945]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_24,plain,
% 47.46/6.48      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 47.46/6.48      inference(cnf_transformation,[],[f110]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_63885,plain,
% 47.46/6.48      ( r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6))
% 47.46/6.48      | k1_xboole_0 = k2_relat_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_24]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_63892,plain,
% 47.46/6.48      ( k1_xboole_0 = k2_relat_1(sK6)
% 47.46/6.48      | r2_hidden(sK1(k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_63885]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_53,negated_conjecture,
% 47.46/6.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
% 47.46/6.48      inference(cnf_transformation,[],[f147]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5360,plain,
% 47.46/6.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_39,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | v1_partfun1(X0,X1)
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | ~ v1_funct_1(X0)
% 47.46/6.48      | k1_xboole_0 = X2 ),
% 47.46/6.48      inference(cnf_transformation,[],[f126]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_31,plain,
% 47.46/6.48      ( ~ v1_partfun1(X0,X1)
% 47.46/6.48      | ~ v4_relat_1(X0,X1)
% 47.46/6.48      | ~ v1_relat_1(X0)
% 47.46/6.48      | k1_relat_1(X0) = X1 ),
% 47.46/6.48      inference(cnf_transformation,[],[f118]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_998,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | ~ v4_relat_1(X0,X1)
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | ~ v1_funct_1(X0)
% 47.46/6.48      | ~ v1_relat_1(X0)
% 47.46/6.48      | k1_relat_1(X0) = X1
% 47.46/6.48      | k1_xboole_0 = X2 ),
% 47.46/6.48      inference(resolution,[status(thm)],[c_39,c_31]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_18,plain,
% 47.46/6.48      ( v4_relat_1(X0,X1)
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 47.46/6.48      inference(cnf_transformation,[],[f105]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_16,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | v1_relat_1(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f104]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_1002,plain,
% 47.46/6.48      ( ~ v1_funct_1(X0)
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | k1_relat_1(X0) = X1
% 47.46/6.48      | k1_xboole_0 = X2 ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_998,c_18,c_16]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_1003,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | ~ v1_funct_1(X0)
% 47.46/6.48      | k1_relat_1(X0) = X1
% 47.46/6.48      | k1_xboole_0 = X2 ),
% 47.46/6.48      inference(renaming,[status(thm)],[c_1002]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5346,plain,
% 47.46/6.48      ( k1_relat_1(X0) = X1
% 47.46/6.48      | k1_xboole_0 = X2
% 47.46/6.48      | v1_funct_2(X0,X1,X2) != iProver_top
% 47.46/6.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.48      | v1_funct_1(X0) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_1003]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6191,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5360,c_5346]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_55,negated_conjecture,
% 47.46/6.48      ( v1_funct_1(sK6) ),
% 47.46/6.48      inference(cnf_transformation,[],[f145]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_54,negated_conjecture,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
% 47.46/6.48      inference(cnf_transformation,[],[f146]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6195,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | ~ v1_funct_1(sK6)
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 47.46/6.48      inference(predicate_to_equality_rev,[status(thm)],[c_6191]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6467,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_6191,c_55,c_54,c_6195]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6471,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0))) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6467,c_5360]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5,plain,
% 47.46/6.48      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 47.46/6.48      inference(cnf_transformation,[],[f151]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6473,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 47.46/6.48      inference(demodulation,[status(thm)],[c_6471,c_5]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_20,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f108]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5380,plain,
% 47.46/6.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 47.46/6.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8235,plain,
% 47.46/6.48      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 47.46/6.48      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5,c_5380]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8780,plain,
% 47.46/6.48      ( k1_relset_1(X0,k1_xboole_0,sK6) = k1_relat_1(sK6)
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6473,c_8235]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_19,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 47.46/6.48      inference(cnf_transformation,[],[f107]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5381,plain,
% 47.46/6.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.48      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_56508,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(X0)) = iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_8780,c_5381]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_56511,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(X0)) = iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.46/6.48      inference(light_normalisation,[status(thm)],[c_56508,c_5]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_56653,plain,
% 47.46/6.48      ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(X0)) = iProver_top
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_56511,c_6473]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_56654,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(X0)) = iProver_top ),
% 47.46/6.48      inference(renaming,[status(thm)],[c_56653]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 47.46/6.48      inference(cnf_transformation,[],[f97]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5385,plain,
% 47.46/6.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.46/6.48      | r1_tarski(X0,X1) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_56659,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_56654,c_5385]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_56831,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_56659]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_48411,plain,
% 47.46/6.48      ( X0 != X1 | X0 = k1_relat_1(sK6) | k1_relat_1(sK6) != X1 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4259]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_48413,plain,
% 47.46/6.48      ( k1_relat_1(sK6) != k1_xboole_0
% 47.46/6.48      | k1_xboole_0 = k1_relat_1(sK6)
% 47.46/6.48      | k1_xboole_0 != k1_xboole_0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_48411]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_4269,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | v1_funct_2(X3,X4,X5)
% 47.46/6.48      | X3 != X0
% 47.46/6.48      | X4 != X1
% 47.46/6.48      | X5 != X2 ),
% 47.46/6.48      theory(equality) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_45243,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | v1_funct_2(sK5,X3,X4)
% 47.46/6.48      | X3 != X1
% 47.46/6.48      | X4 != X2
% 47.46/6.48      | sK5 != X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4269]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_46614,plain,
% 47.46/6.48      ( v1_funct_2(sK5,X0,X1)
% 47.46/6.48      | ~ v1_funct_2(sK6,X2,X3)
% 47.46/6.48      | X0 != X2
% 47.46/6.48      | X1 != X3
% 47.46/6.48      | sK5 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_45243]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_47555,plain,
% 47.46/6.48      ( v1_funct_2(sK5,X0,X1)
% 47.46/6.48      | ~ v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6))
% 47.46/6.48      | X0 != k1_relat_1(sK6)
% 47.46/6.48      | X1 != k2_relat_1(sK6)
% 47.46/6.48      | sK5 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_46614]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_47556,plain,
% 47.46/6.48      ( X0 != k1_relat_1(sK6)
% 47.46/6.48      | X1 != k2_relat_1(sK6)
% 47.46/6.48      | sK5 != sK6
% 47.46/6.48      | v1_funct_2(sK5,X0,X1) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_47555]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_47558,plain,
% 47.46/6.48      ( sK5 != sK6
% 47.46/6.48      | k1_xboole_0 != k1_relat_1(sK6)
% 47.46/6.48      | k1_xboole_0 != k2_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) != iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_47556]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_45464,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | v1_funct_2(sK6,X3,X4)
% 47.46/6.48      | X3 != X1
% 47.46/6.48      | X4 != X2
% 47.46/6.48      | sK6 != X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4269]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_46946,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK5,X0,X1)
% 47.46/6.48      | v1_funct_2(sK6,X2,X3)
% 47.46/6.48      | X2 != X0
% 47.46/6.48      | X3 != X1
% 47.46/6.48      | sK6 != sK5 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_45464]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_46947,plain,
% 47.46/6.48      ( X0 != X1
% 47.46/6.48      | X2 != X3
% 47.46/6.48      | sK6 != sK5
% 47.46/6.48      | v1_funct_2(sK5,X1,X3) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,X0,X2) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_46946]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_46949,plain,
% 47.46/6.48      ( sK6 != sK5
% 47.46/6.48      | k1_xboole_0 != k1_xboole_0
% 47.46/6.48      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_46947]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9007,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | v1_funct_2(sK6,X3,X4)
% 47.46/6.48      | X3 != X1
% 47.46/6.48      | X4 != X2
% 47.46/6.48      | sK6 != X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4269]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_12992,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 47.46/6.48      | v1_funct_2(sK6,X1,X2)
% 47.46/6.48      | X1 != k1_relat_1(X0)
% 47.46/6.48      | X2 != k2_relat_1(X0)
% 47.46/6.48      | sK6 != X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_9007]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_22296,plain,
% 47.46/6.48      ( v1_funct_2(sK6,X0,X1)
% 47.46/6.48      | ~ v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6))
% 47.46/6.48      | X0 != k1_relat_1(sK6)
% 47.46/6.48      | X1 != k2_relat_1(sK6)
% 47.46/6.48      | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_12992]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_28807,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0)
% 47.46/6.48      | ~ v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6))
% 47.46/6.48      | X0 != k2_relat_1(sK6)
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_relat_1(sK6)
% 47.46/6.48      | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_22296]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_28808,plain,
% 47.46/6.48      ( X0 != k2_relat_1(sK6)
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_relat_1(sK6)
% 47.46/6.48      | sK6 != sK6
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_28807]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_28810,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_relat_1(sK6)
% 47.46/6.48      | sK6 != sK6
% 47.46/6.48      | k1_xboole_0 != k2_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) != iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_28808]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_12654,plain,
% 47.46/6.48      ( X0 != X1 | X0 = u1_struct_0(sK4) | u1_struct_0(sK4) != X1 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4259]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_23979,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4)
% 47.46/6.48      | u1_struct_0(sK4) != X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_12654]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_23980,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4)
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0
% 47.46/6.48      | u1_struct_0(sK4) != k1_xboole_0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_23979]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_4,plain,
% 47.46/6.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 47.46/6.48      inference(cnf_transformation,[],[f92]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_20904,plain,
% 47.46/6.48      ( ~ v1_xboole_0(u1_struct_0(sK3))
% 47.46/6.48      | k1_xboole_0 = u1_struct_0(sK3) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_20170,plain,
% 47.46/6.48      ( ~ v1_xboole_0(u1_struct_0(sK4))
% 47.46/6.48      | k1_xboole_0 = u1_struct_0(sK4) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_21,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 47.46/6.48      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 47.46/6.48      inference(cnf_transformation,[],[f109]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5379,plain,
% 47.46/6.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10856,plain,
% 47.46/6.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5360,c_5379]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_47,plain,
% 47.46/6.48      ( ~ v5_pre_topc(X0,X1,X2)
% 47.46/6.48      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 47.46/6.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.46/6.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 47.46/6.48      | ~ v2_pre_topc(X1)
% 47.46/6.48      | ~ v2_pre_topc(X2)
% 47.46/6.48      | ~ l1_pre_topc(X1)
% 47.46/6.48      | ~ l1_pre_topc(X2)
% 47.46/6.48      | ~ v1_funct_1(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f156]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5365,plain,
% 47.46/6.48      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 47.46/6.48      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 47.46/6.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 47.46/6.48      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 47.46/6.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 47.46/6.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(X1) != iProver_top
% 47.46/6.48      | v2_pre_topc(X2) != iProver_top
% 47.46/6.48      | l1_pre_topc(X1) != iProver_top
% 47.46/6.48      | l1_pre_topc(X2) != iProver_top
% 47.46/6.48      | v1_funct_1(X0) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_11256,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(X0) != iProver_top
% 47.46/6.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | l1_pre_topc(X0) != iProver_top
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_10856,c_5365]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_60,negated_conjecture,
% 47.46/6.48      ( v2_pre_topc(sK4) ),
% 47.46/6.48      inference(cnf_transformation,[],[f140]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_65,plain,
% 47.46/6.48      ( v2_pre_topc(sK4) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_59,negated_conjecture,
% 47.46/6.48      ( l1_pre_topc(sK4) ),
% 47.46/6.48      inference(cnf_transformation,[],[f141]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_66,plain,
% 47.46/6.48      ( l1_pre_topc(sK4) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_70,plain,
% 47.46/6.48      ( v1_funct_1(sK6) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_45,plain,
% 47.46/6.48      ( ~ v2_pre_topc(X0)
% 47.46/6.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 47.46/6.48      | ~ l1_pre_topc(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f133]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5534,plain,
% 47.46/6.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | ~ v2_pre_topc(sK4)
% 47.46/6.48      | ~ l1_pre_topc(sK4) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_45]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5535,plain,
% 47.46/6.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v2_pre_topc(sK4) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK4) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5534]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_43,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 47.46/6.48      inference(cnf_transformation,[],[f131]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5612,plain,
% 47.46/6.48      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_43]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5613,plain,
% 47.46/6.48      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5612]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_44,plain,
% 47.46/6.48      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 47.46/6.48      | ~ l1_pre_topc(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f132]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5789,plain,
% 47.46/6.48      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 47.46/6.48      | ~ l1_pre_topc(sK4) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_44]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5790,plain,
% 47.46/6.48      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 47.46/6.48      | l1_pre_topc(sK4) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5789]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_12305,plain,
% 47.46/6.48      ( v2_pre_topc(X0) != iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | l1_pre_topc(X0) != iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_11256,c_65,c_66,c_70,c_5535,c_5613,c_5790]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_12306,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(X0) != iProver_top
% 47.46/6.48      | l1_pre_topc(X0) != iProver_top ),
% 47.46/6.48      inference(renaming,[status(thm)],[c_12305]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_12313,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK4) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK4) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6467,c_12306]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_3,plain,
% 47.46/6.48      ( v1_xboole_0(k1_xboole_0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f91]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_190,plain,
% 47.46/6.48      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5684,plain,
% 47.46/6.48      ( r2_hidden(sK1(sK6),sK6) | k1_xboole_0 = sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_24]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5688,plain,
% 47.46/6.48      ( k1_xboole_0 = sK6 | r2_hidden(sK1(sK6),sK6) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5684]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5719,plain,
% 47.46/6.48      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4259]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6204,plain,
% 47.46/6.48      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_5719]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6205,plain,
% 47.46/6.48      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_6204]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5359,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6472,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6467,c_5359]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_4258,plain,( X0 = X0 ),theory(equality) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6500,plain,
% 47.46/6.48      ( sK6 = sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4258]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6870,plain,
% 47.46/6.48      ( ~ r2_hidden(sK1(sK6),sK6)
% 47.46/6.48      | ~ r1_tarski(sK6,X0)
% 47.46/6.48      | ~ v1_xboole_0(X0) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_554]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6871,plain,
% 47.46/6.48      ( r2_hidden(sK1(sK6),sK6) != iProver_top
% 47.46/6.48      | r1_tarski(sK6,X0) != iProver_top
% 47.46/6.48      | v1_xboole_0(X0) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_6870]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6873,plain,
% 47.46/6.48      ( r2_hidden(sK1(sK6),sK6) != iProver_top
% 47.46/6.48      | r1_tarski(sK6,k1_xboole_0) != iProver_top
% 47.46/6.48      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_6871]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_4262,plain,
% 47.46/6.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 47.46/6.48      theory(equality) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6876,plain,
% 47.46/6.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4262]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6878,plain,
% 47.46/6.48      ( v1_xboole_0(sK6)
% 47.46/6.48      | ~ v1_xboole_0(k1_xboole_0)
% 47.46/6.48      | sK6 != k1_xboole_0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_6876]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7078,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6473,c_5385]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_56,negated_conjecture,
% 47.46/6.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 47.46/6.48      inference(cnf_transformation,[],[f144]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5357,plain,
% 47.46/6.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_52,negated_conjecture,
% 47.46/6.48      ( sK5 = sK6 ),
% 47.46/6.48      inference(cnf_transformation,[],[f148]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5395,plain,
% 47.46/6.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 47.46/6.48      inference(light_normalisation,[status(thm)],[c_5357,c_52]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_28,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | ~ v1_funct_1(X0)
% 47.46/6.48      | ~ v1_xboole_0(X0)
% 47.46/6.48      | v1_xboole_0(X1)
% 47.46/6.48      | v1_xboole_0(X2) ),
% 47.46/6.48      inference(cnf_transformation,[],[f116]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_15,plain,
% 47.46/6.48      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f103]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_348,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | ~ v1_xboole_0(X0)
% 47.46/6.48      | v1_xboole_0(X1)
% 47.46/6.48      | v1_xboole_0(X2) ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_28,c_15]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_349,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | ~ v1_xboole_0(X0)
% 47.46/6.48      | v1_xboole_0(X1)
% 47.46/6.48      | v1_xboole_0(X2) ),
% 47.46/6.48      inference(renaming,[status(thm)],[c_348]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5350,plain,
% 47.46/6.48      ( v1_funct_2(X0,X1,X2) != iProver_top
% 47.46/6.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.48      | v1_xboole_0(X0) != iProver_top
% 47.46/6.48      | v1_xboole_0(X1) = iProver_top
% 47.46/6.48      | v1_xboole_0(X2) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6945,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
% 47.46/6.48      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 47.46/6.48      | v1_xboole_0(sK6) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5395,c_5350]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_57,negated_conjecture,
% 47.46/6.48      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 47.46/6.48      inference(cnf_transformation,[],[f143]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5356,plain,
% 47.46/6.48      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5394,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 47.46/6.48      inference(light_normalisation,[status(thm)],[c_5356,c_52]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7235,plain,
% 47.46/6.48      ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top
% 47.46/6.48      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 47.46/6.48      | v1_xboole_0(sK6) != iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_6945,c_5394]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5388,plain,
% 47.46/6.48      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7241,plain,
% 47.46/6.48      ( u1_struct_0(sK4) = k1_xboole_0
% 47.46/6.48      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 47.46/6.48      | v1_xboole_0(sK6) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_7235,c_5388]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7357,plain,
% 47.46/6.48      ( u1_struct_0(sK4) = k1_xboole_0
% 47.46/6.48      | u1_struct_0(sK3) = k1_xboole_0
% 47.46/6.48      | v1_xboole_0(sK6) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_7241,c_5388]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7359,plain,
% 47.46/6.48      ( ~ v1_xboole_0(sK6)
% 47.46/6.48      | u1_struct_0(sK4) = k1_xboole_0
% 47.46/6.48      | u1_struct_0(sK3) = k1_xboole_0 ),
% 47.46/6.48      inference(predicate_to_equality_rev,[status(thm)],[c_7357]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8232,plain,
% 47.46/6.48      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK6) = k1_relat_1(sK6) ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5395,c_5380]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8833,plain,
% 47.46/6.48      ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_8232,c_5381]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9043,plain,
% 47.46/6.48      ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_8833,c_5395]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9047,plain,
% 47.46/6.48      ( r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3)) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_9043,c_5385]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8231,plain,
% 47.46/6.48      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6) = k1_relat_1(sK6) ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5360,c_5380]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8832,plain,
% 47.46/6.48      ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) = iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_8231,c_5381]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_72,plain,
% 47.46/6.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9169,plain,
% 47.46/6.48      ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) = iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_8832,c_72]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9174,plain,
% 47.46/6.48      ( r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_9169,c_5385]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6227,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != X1
% 47.46/6.48      | u1_struct_0(sK4) != X2
% 47.46/6.48      | sK6 != X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4269]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7606,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,X0,X1)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != X0
% 47.46/6.48      | u1_struct_0(sK4) != X1
% 47.46/6.48      | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_6227]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10381,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 47.46/6.48      | u1_struct_0(sK4) != X0
% 47.46/6.48      | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_7606]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10382,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 47.46/6.48      | u1_struct_0(sK4) != X0
% 47.46/6.48      | sK6 != sK6
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_10381]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10384,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 47.46/6.48      | u1_struct_0(sK4) != k1_xboole_0
% 47.46/6.48      | sK6 != sK6
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_10382]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10857,plain,
% 47.46/6.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK4)))) = iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5395,c_5379]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_49,plain,
% 47.46/6.48      ( ~ v5_pre_topc(X0,X1,X2)
% 47.46/6.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 47.46/6.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.46/6.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 47.46/6.48      | ~ v2_pre_topc(X1)
% 47.46/6.48      | ~ v2_pre_topc(X2)
% 47.46/6.48      | ~ l1_pre_topc(X1)
% 47.46/6.48      | ~ l1_pre_topc(X2)
% 47.46/6.48      | ~ v1_funct_1(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f158]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5363,plain,
% 47.46/6.48      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 47.46/6.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 47.46/6.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 47.46/6.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 47.46/6.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 47.46/6.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 47.46/6.48      | v2_pre_topc(X1) != iProver_top
% 47.46/6.48      | v2_pre_topc(X2) != iProver_top
% 47.46/6.48      | l1_pre_topc(X1) != iProver_top
% 47.46/6.48      | l1_pre_topc(X2) != iProver_top
% 47.46/6.48      | v1_funct_1(X0) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7426,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK4) != iProver_top
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK4) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5360,c_5363]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_62,negated_conjecture,
% 47.46/6.48      ( v2_pre_topc(sK3) ),
% 47.46/6.48      inference(cnf_transformation,[],[f138]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_63,plain,
% 47.46/6.48      ( v2_pre_topc(sK3) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_61,negated_conjecture,
% 47.46/6.48      ( l1_pre_topc(sK3) ),
% 47.46/6.48      inference(cnf_transformation,[],[f139]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_64,plain,
% 47.46/6.48      ( l1_pre_topc(sK3) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_71,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_51,negated_conjecture,
% 47.46/6.48      ( v5_pre_topc(sK5,sK3,sK4)
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 47.46/6.48      inference(cnf_transformation,[],[f149]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5361,plain,
% 47.46/6.48      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5396,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
% 47.46/6.48      inference(light_normalisation,[status(thm)],[c_5361,c_52]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_50,negated_conjecture,
% 47.46/6.48      ( ~ v5_pre_topc(sK5,sK3,sK4)
% 47.46/6.48      | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 47.46/6.48      inference(cnf_transformation,[],[f150]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5362,plain,
% 47.46/6.48      ( v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5397,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
% 47.46/6.48      inference(light_normalisation,[status(thm)],[c_5362,c_52]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5519,plain,
% 47.46/6.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 47.46/6.48      | ~ v2_pre_topc(sK3)
% 47.46/6.48      | ~ l1_pre_topc(sK3) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_45]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5520,plain,
% 47.46/6.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 47.46/6.48      | v2_pre_topc(sK3) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK3) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5519]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5602,plain,
% 47.46/6.48      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_43]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5603,plain,
% 47.46/6.48      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5602]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5731,plain,
% 47.46/6.48      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 47.46/6.48      | ~ l1_pre_topc(sK3) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_44]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5732,plain,
% 47.46/6.48      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 47.46/6.48      | l1_pre_topc(sK3) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5731]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_48,plain,
% 47.46/6.48      ( v5_pre_topc(X0,X1,X2)
% 47.46/6.48      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 47.46/6.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.46/6.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 47.46/6.48      | ~ v2_pre_topc(X1)
% 47.46/6.48      | ~ v2_pre_topc(X2)
% 47.46/6.48      | ~ l1_pre_topc(X1)
% 47.46/6.48      | ~ l1_pre_topc(X2)
% 47.46/6.48      | ~ v1_funct_1(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f157]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5628,plain,
% 47.46/6.48      ( ~ v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | v5_pre_topc(sK6,X0,sK4)
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 47.46/6.48      | ~ v2_pre_topc(X0)
% 47.46/6.48      | ~ v2_pre_topc(sK4)
% 47.46/6.48      | ~ l1_pre_topc(X0)
% 47.46/6.48      | ~ l1_pre_topc(sK4)
% 47.46/6.48      | ~ v1_funct_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_48]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5871,plain,
% 47.46/6.48      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 47.46/6.48      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 47.46/6.48      | ~ v2_pre_topc(sK4)
% 47.46/6.48      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 47.46/6.48      | ~ l1_pre_topc(sK4)
% 47.46/6.48      | ~ v1_funct_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_5628]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5872,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK4) != iProver_top
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK4) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5871]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_46,plain,
% 47.46/6.48      ( v5_pre_topc(X0,X1,X2)
% 47.46/6.48      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 47.46/6.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.46/6.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 47.46/6.48      | ~ v2_pre_topc(X1)
% 47.46/6.48      | ~ v2_pre_topc(X2)
% 47.46/6.48      | ~ l1_pre_topc(X1)
% 47.46/6.48      | ~ l1_pre_topc(X2)
% 47.46/6.48      | ~ v1_funct_1(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f155]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5627,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,X0,sK4)
% 47.46/6.48      | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
% 47.46/6.48      | ~ v2_pre_topc(X0)
% 47.46/6.48      | ~ v2_pre_topc(sK4)
% 47.46/6.48      | ~ l1_pre_topc(X0)
% 47.46/6.48      | ~ l1_pre_topc(sK4)
% 47.46/6.48      | ~ v1_funct_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_46]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5894,plain,
% 47.46/6.48      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 47.46/6.48      | v5_pre_topc(sK6,sK3,sK4)
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 47.46/6.48      | ~ v2_pre_topc(sK4)
% 47.46/6.48      | ~ v2_pre_topc(sK3)
% 47.46/6.48      | ~ l1_pre_topc(sK4)
% 47.46/6.48      | ~ l1_pre_topc(sK3)
% 47.46/6.48      | ~ v1_funct_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_5627]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5895,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK4) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK3) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK4) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK3) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5894]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5859,plain,
% 47.46/6.48      ( ~ v5_pre_topc(sK6,X0,sK4)
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
% 47.46/6.48      | ~ v2_pre_topc(X0)
% 47.46/6.48      | ~ v2_pre_topc(sK4)
% 47.46/6.48      | ~ l1_pre_topc(X0)
% 47.46/6.48      | ~ l1_pre_topc(sK4)
% 47.46/6.48      | ~ v1_funct_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_47]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6434,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 47.46/6.48      | ~ v5_pre_topc(sK6,sK3,sK4)
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 47.46/6.48      | ~ v2_pre_topc(sK4)
% 47.46/6.48      | ~ v2_pre_topc(sK3)
% 47.46/6.48      | ~ l1_pre_topc(sK4)
% 47.46/6.48      | ~ l1_pre_topc(sK3)
% 47.46/6.48      | ~ v1_funct_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_5859]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6435,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK3,sK4) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK4) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK3) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK4) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK3) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_6434]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7779,plain,
% 47.46/6.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_7426,c_63,c_64,c_65,c_66,c_70,c_71,c_72,c_5396,c_5394,
% 47.46/6.48                 c_5395,c_5397,c_5520,c_5603,c_5732,c_5872,c_5895,c_6435]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7780,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 47.46/6.48      inference(renaming,[status(thm)],[c_7779]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7783,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_7780,c_63,c_64,c_65,c_66,c_70,c_71,c_72,c_5396,c_5394,
% 47.46/6.48                 c_5395,c_5520,c_5603,c_5732,c_5872,c_6435]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_11135,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_10857,c_7783]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8731,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK3) != iProver_top
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK3) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5360,c_5365]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5868,plain,
% 47.46/6.48      ( ~ v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | v5_pre_topc(sK6,sK3,sK4)
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 47.46/6.48      | ~ v2_pre_topc(sK4)
% 47.46/6.48      | ~ v2_pre_topc(sK3)
% 47.46/6.48      | ~ l1_pre_topc(sK4)
% 47.46/6.48      | ~ l1_pre_topc(sK3)
% 47.46/6.48      | ~ v1_funct_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_5628]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5869,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK4) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK3) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK4) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK3) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5868]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5931,plain,
% 47.46/6.48      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 47.46/6.48      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | ~ v2_pre_topc(sK3)
% 47.46/6.48      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | ~ l1_pre_topc(sK3)
% 47.46/6.48      | ~ v1_funct_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_46]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5935,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK3) != iProver_top
% 47.46/6.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK3) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5931]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5937,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | ~ v5_pre_topc(sK6,sK3,sK4)
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 47.46/6.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 47.46/6.48      | ~ v2_pre_topc(sK4)
% 47.46/6.48      | ~ v2_pre_topc(sK3)
% 47.46/6.48      | ~ l1_pre_topc(sK4)
% 47.46/6.48      | ~ l1_pre_topc(sK3)
% 47.46/6.48      | ~ v1_funct_1(sK6) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_49]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5938,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK3,sK4) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK4) != iProver_top
% 47.46/6.48      | v2_pre_topc(sK3) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK4) != iProver_top
% 47.46/6.48      | l1_pre_topc(sK3) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_5937]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8938,plain,
% 47.46/6.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_8731,c_63,c_64,c_65,c_66,c_70,c_71,c_72,c_5396,c_5394,
% 47.46/6.48                 c_5395,c_5397,c_5535,c_5613,c_5790,c_5869,c_5935,c_5938]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8939,plain,
% 47.46/6.48      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 47.46/6.48      inference(renaming,[status(thm)],[c_8938]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8942,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_8939,c_63,c_64,c_65,c_66,c_70,c_71,c_72,c_5396,c_5394,
% 47.46/6.48                 c_5395,c_5535,c_5613,c_5790,c_5935,c_5938]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_11260,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3)) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_10856,c_8942]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_12153,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4258]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6061,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X2
% 47.46/6.48      | u1_struct_0(sK3) != X1
% 47.46/6.48      | sK6 != X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4269]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7170,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,X0,X1)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X1
% 47.46/6.48      | u1_struct_0(sK3) != X0
% 47.46/6.48      | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_6061]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_16350,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | u1_struct_0(sK3) != X0
% 47.46/6.48      | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_7170]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_16351,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | u1_struct_0(sK3) != X0
% 47.46/6.48      | sK6 != sK6
% 47.46/6.48      | v1_funct_2(sK6,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_16350]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_16353,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | u1_struct_0(sK3) != k1_xboole_0
% 47.46/6.48      | sK6 != sK6
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_16351]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_20034,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4258]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_20057,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_12313,c_3,c_190,c_5688,c_6205,c_6472,c_6500,c_6873,
% 47.46/6.48                 c_6878,c_7078,c_7359,c_9047,c_9174,c_10384,c_11135,
% 47.46/6.48                 c_11260,c_12153,c_16353,c_20034]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_20061,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6467,c_20057]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_12982,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 47.46/6.48      | v1_funct_2(sK6,X0,X1)
% 47.46/6.48      | X1 != u1_struct_0(sK4)
% 47.46/6.48      | X0 != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK5 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_9007]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_19760,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 47.46/6.48      | v1_funct_2(sK6,X0,u1_struct_0(sK4))
% 47.46/6.48      | X0 != u1_struct_0(sK3)
% 47.46/6.48      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 47.46/6.48      | sK6 != sK5 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_12982]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_19761,plain,
% 47.46/6.48      ( X0 != u1_struct_0(sK3)
% 47.46/6.48      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 47.46/6.48      | sK6 != sK5
% 47.46/6.48      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,X0,u1_struct_0(sK4)) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_19760]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_19763,plain,
% 47.46/6.48      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 47.46/6.48      | sK6 != sK5
% 47.46/6.48      | k1_xboole_0 != u1_struct_0(sK3)
% 47.46/6.48      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(sK4)) = iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_19761]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8716,plain,
% 47.46/6.48      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),X3)
% 47.46/6.48      | X3 != X2
% 47.46/6.48      | u1_struct_0(sK3) != X1
% 47.46/6.48      | sK6 != X0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4269]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_15141,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),X0)
% 47.46/6.48      | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 47.46/6.48      | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_8716]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_19597,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 47.46/6.48      | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_15141]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_15146,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),X0)
% 47.46/6.48      | X0 != u1_struct_0(sK4)
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK5 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_8716]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_15147,plain,
% 47.46/6.48      ( X0 != u1_struct_0(sK4)
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK5
% 47.46/6.48      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),X0) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_15146]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_15149,plain,
% 47.46/6.48      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK5
% 47.46/6.48      | k1_xboole_0 != u1_struct_0(sK4)
% 47.46/6.48      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) = iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_15147]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6192,plain,
% 47.46/6.48      ( u1_struct_0(sK4) = k1_xboole_0
% 47.46/6.48      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5395,c_5346]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6248,plain,
% 47.46/6.48      ( u1_struct_0(sK4) = k1_xboole_0
% 47.46/6.48      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_6192,c_70,c_5394]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5386,plain,
% 47.46/6.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 47.46/6.48      | r1_tarski(X0,X1) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7787,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5386,c_7783]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7796,plain,
% 47.46/6.48      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6248,c_7787]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7797,plain,
% 47.46/6.48      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
% 47.46/6.48      inference(demodulation,[status(thm)],[c_7796,c_5]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_11658,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_7797,c_9174,c_11135]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_11663,plain,
% 47.46/6.48      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6248,c_11658]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_11290,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | ~ r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3)) ),
% 47.46/6.48      inference(predicate_to_equality_rev,[status(thm)],[c_11260]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_11130,plain,
% 47.46/6.48      ( u1_struct_0(sK4) = k1_xboole_0
% 47.46/6.48      | k1_relat_1(sK6) = X0
% 47.46/6.48      | v1_funct_2(sK6,X0,u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_10857,c_5346]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_11146,plain,
% 47.46/6.48      ( u1_struct_0(sK4) = k1_xboole_0
% 47.46/6.48      | k1_relat_1(sK6) = k1_xboole_0
% 47.46/6.48      | v1_funct_2(sK6,k1_xboole_0,u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top
% 47.46/6.48      | v1_funct_1(sK6) != iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_11130]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8946,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5386,c_8942]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9051,plain,
% 47.46/6.48      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))))) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6248,c_8946]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9178,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) != iProver_top
% 47.46/6.48      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))))) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6467,c_9051]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8380,plain,
% 47.46/6.48      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4258]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8947,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) != iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6467,c_8942]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8949,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 47.46/6.48      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.46/6.48      inference(demodulation,[status(thm)],[c_8947,c_5]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10156,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),X0)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_7170]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10157,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK6
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),X0) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_10156]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10159,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK6
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) != iProver_top ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_10157]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10600,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) != iProver_top
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_9178,c_6467,c_6473,c_6500,c_8380,c_8949,c_10159]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_10601,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),k1_xboole_0) != iProver_top ),
% 47.46/6.48      inference(renaming,[status(thm)],[c_10600]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7175,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK5,X0,X1)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X1
% 47.46/6.48      | u1_struct_0(sK3) != X0
% 47.46/6.48      | sK6 != sK5 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_6061]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8069,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),X0)
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK5 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_7175]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9784,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 47.46/6.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(sK4)
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK5 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_8069]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9785,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(sK4)
% 47.46/6.48      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.46/6.48      | sK6 != sK5
% 47.46/6.48      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 47.46/6.48      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_9784]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_9048,plain,
% 47.46/6.48      ( r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3)) ),
% 47.46/6.48      inference(predicate_to_equality_rev,[status(thm)],[c_9047]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_8356,plain,
% 47.46/6.48      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4258]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5382,plain,
% 47.46/6.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.48      | v1_relat_1(X0) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7566,plain,
% 47.46/6.48      ( v1_relat_1(sK6) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5360,c_5382]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6952,plain,
% 47.46/6.48      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 47.46/6.48      | v1_xboole_0(u1_struct_0(sK4))
% 47.46/6.48      | v1_xboole_0(u1_struct_0(sK3))
% 47.46/6.48      | ~ v1_xboole_0(sK6) ),
% 47.46/6.48      inference(predicate_to_equality_rev,[status(thm)],[c_6945]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_17,plain,
% 47.46/6.48      ( v5_relat_1(X0,X1)
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 47.46/6.48      inference(cnf_transformation,[],[f106]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_14,plain,
% 47.46/6.48      ( ~ v5_relat_1(X0,X1)
% 47.46/6.48      | r1_tarski(k2_relat_1(X0),X1)
% 47.46/6.48      | ~ v1_relat_1(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f101]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_745,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | r1_tarski(k2_relat_1(X0),X2)
% 47.46/6.48      | ~ v1_relat_1(X0) ),
% 47.46/6.48      inference(resolution,[status(thm)],[c_17,c_14]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_749,plain,
% 47.46/6.48      ( r1_tarski(k2_relat_1(X0),X2)
% 47.46/6.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 47.46/6.48      inference(global_propositional_subsumption,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_745,c_16]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_750,plain,
% 47.46/6.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.48      | r1_tarski(k2_relat_1(X0),X2) ),
% 47.46/6.48      inference(renaming,[status(thm)],[c_749]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5348,plain,
% 47.46/6.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.48      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6484,plain,
% 47.46/6.48      ( r1_tarski(k2_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5360,c_5348]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6672,plain,
% 47.46/6.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 47.46/6.48      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6467,c_6484]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6485,plain,
% 47.46/6.48      ( r1_tarski(k2_relat_1(sK6),u1_struct_0(sK4)) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_5395,c_5348]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6613,plain,
% 47.46/6.48      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 47.46/6.48      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) = iProver_top ),
% 47.46/6.48      inference(superposition,[status(thm)],[c_6248,c_6485]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5663,plain,
% 47.46/6.48      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_4259]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5908,plain,
% 47.46/6.48      ( X0 = sK5 | X0 != sK6 | sK5 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_5663]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5959,plain,
% 47.46/6.48      ( sK5 != sK6 | sK6 = sK5 | sK6 != sK6 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_5908]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_5420,plain,
% 47.46/6.48      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 47.46/6.48      inference(predicate_to_equality_rev,[status(thm)],[c_5394]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_41,plain,
% 47.46/6.48      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 47.46/6.48      | ~ v1_funct_1(X0)
% 47.46/6.48      | ~ v1_relat_1(X0) ),
% 47.46/6.48      inference(cnf_transformation,[],[f129]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_2077,plain,
% 47.46/6.48      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 47.46/6.48      | ~ v1_relat_1(X0)
% 47.46/6.48      | sK6 != X0 ),
% 47.46/6.48      inference(resolution_lifted,[status(thm)],[c_41,c_55]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_2078,plain,
% 47.46/6.48      ( v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6))
% 47.46/6.48      | ~ v1_relat_1(sK6) ),
% 47.46/6.48      inference(unflattening,[status(thm)],[c_2077]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_2079,plain,
% 47.46/6.48      ( v1_funct_2(sK6,k1_relat_1(sK6),k2_relat_1(sK6)) = iProver_top
% 47.46/6.48      | v1_relat_1(sK6) != iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_2078]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_6,plain,
% 47.46/6.48      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 47.46/6.48      inference(cnf_transformation,[],[f152]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_186,plain,
% 47.46/6.48      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_6]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_7,plain,
% 47.46/6.48      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 47.46/6.48      | k1_xboole_0 = X0
% 47.46/6.48      | k1_xboole_0 = X1 ),
% 47.46/6.48      inference(cnf_transformation,[],[f93]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_185,plain,
% 47.46/6.48      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 47.46/6.48      | k1_xboole_0 = k1_xboole_0 ),
% 47.46/6.48      inference(instantiation,[status(thm)],[c_7]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(c_68,plain,
% 47.46/6.48      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 47.46/6.48      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 47.46/6.48  
% 47.46/6.48  cnf(contradiction,plain,
% 47.46/6.48      ( $false ),
% 47.46/6.48      inference(minisat,
% 47.46/6.48                [status(thm)],
% 47.46/6.48                [c_93570,c_64305,c_63892,c_56831,c_48413,c_47558,c_46949,
% 47.46/6.48                 c_28810,c_23980,c_20904,c_20170,c_20061,c_20034,c_19763,
% 47.46/6.48                 c_19597,c_15149,c_11663,c_11290,c_11260,c_11146,c_10601,
% 47.46/6.48                 c_9785,c_9048,c_9047,c_8380,c_8356,c_7566,c_7078,c_6952,
% 47.46/6.48                 c_6878,c_6873,c_6672,c_6613,c_6500,c_6467,c_6205,c_5959,
% 47.46/6.48                 c_5688,c_5420,c_2079,c_190,c_3,c_186,c_185,c_52,c_54,
% 47.46/6.48                 c_70,c_68]) ).
% 47.46/6.48  
% 47.46/6.48  
% 47.46/6.48  % SZS output end CNFRefutation for theBenchmark.p
% 47.46/6.48  
% 47.46/6.48  ------                               Statistics
% 47.46/6.48  
% 47.46/6.48  ------ General
% 47.46/6.48  
% 47.46/6.48  abstr_ref_over_cycles:                  0
% 47.46/6.48  abstr_ref_under_cycles:                 0
% 47.46/6.48  gc_basic_clause_elim:                   0
% 47.46/6.48  forced_gc_time:                         0
% 47.46/6.48  parsing_time:                           0.013
% 47.46/6.48  unif_index_cands_time:                  0.
% 47.46/6.48  unif_index_add_time:                    0.
% 47.46/6.48  orderings_time:                         0.
% 47.46/6.48  out_proof_time:                         0.031
% 47.46/6.48  total_time:                             5.831
% 47.46/6.48  num_of_symbols:                         62
% 47.46/6.48  num_of_terms:                           112725
% 47.46/6.48  
% 47.46/6.48  ------ Preprocessing
% 47.46/6.48  
% 47.46/6.48  num_of_splits:                          0
% 47.46/6.48  num_of_split_atoms:                     1
% 47.46/6.48  num_of_reused_defs:                     0
% 47.46/6.48  num_eq_ax_congr_red:                    48
% 47.46/6.48  num_of_sem_filtered_clauses:            1
% 47.46/6.48  num_of_subtypes:                        0
% 47.46/6.48  monotx_restored_types:                  0
% 47.46/6.48  sat_num_of_epr_types:                   0
% 47.46/6.48  sat_num_of_non_cyclic_types:            0
% 47.46/6.48  sat_guarded_non_collapsed_types:        0
% 47.46/6.48  num_pure_diseq_elim:                    0
% 47.46/6.48  simp_replaced_by:                       0
% 47.46/6.48  res_preprocessed:                       255
% 47.46/6.48  prep_upred:                             0
% 47.46/6.48  prep_unflattend:                        137
% 47.46/6.48  smt_new_axioms:                         0
% 47.46/6.48  pred_elim_cands:                        10
% 47.46/6.48  pred_elim:                              3
% 47.46/6.48  pred_elim_cl:                           6
% 47.46/6.48  pred_elim_cycles:                       11
% 47.46/6.48  merged_defs:                            16
% 47.46/6.48  merged_defs_ncl:                        0
% 47.46/6.48  bin_hyper_res:                          17
% 47.46/6.48  prep_cycles:                            4
% 47.46/6.48  pred_elim_time:                         0.064
% 47.46/6.48  splitting_time:                         0.
% 47.46/6.48  sem_filter_time:                        0.
% 47.46/6.48  monotx_time:                            0.001
% 47.46/6.48  subtype_inf_time:                       0.
% 47.46/6.48  
% 47.46/6.48  ------ Problem properties
% 47.46/6.48  
% 47.46/6.48  clauses:                                53
% 47.46/6.48  conjectures:                            13
% 47.46/6.48  epr:                                    12
% 47.46/6.48  horn:                                   46
% 47.46/6.48  ground:                                 14
% 47.46/6.48  unary:                                  20
% 47.46/6.48  binary:                                 15
% 47.46/6.48  lits:                                   143
% 47.46/6.48  lits_eq:                                17
% 47.46/6.48  fd_pure:                                0
% 47.46/6.48  fd_pseudo:                              0
% 47.46/6.48  fd_cond:                                5
% 47.46/6.48  fd_pseudo_cond:                         2
% 47.46/6.48  ac_symbols:                             0
% 47.46/6.48  
% 47.46/6.48  ------ Propositional Solver
% 47.46/6.48  
% 47.46/6.48  prop_solver_calls:                      51
% 47.46/6.48  prop_fast_solver_calls:                 13650
% 47.46/6.48  smt_solver_calls:                       0
% 47.46/6.48  smt_fast_solver_calls:                  0
% 47.46/6.48  prop_num_of_clauses:                    37077
% 47.46/6.48  prop_preprocess_simplified:             55114
% 47.46/6.48  prop_fo_subsumed:                       1064
% 47.46/6.48  prop_solver_time:                       0.
% 47.46/6.48  smt_solver_time:                        0.
% 47.46/6.48  smt_fast_solver_time:                   0.
% 47.46/6.48  prop_fast_solver_time:                  0.
% 47.46/6.48  prop_unsat_core_time:                   0.004
% 47.46/6.48  
% 47.46/6.48  ------ QBF
% 47.46/6.48  
% 47.46/6.48  qbf_q_res:                              0
% 47.46/6.48  qbf_num_tautologies:                    0
% 47.46/6.48  qbf_prep_cycles:                        0
% 47.46/6.48  
% 47.46/6.48  ------ BMC1
% 47.46/6.48  
% 47.46/6.48  bmc1_current_bound:                     -1
% 47.46/6.48  bmc1_last_solved_bound:                 -1
% 47.46/6.48  bmc1_unsat_core_size:                   -1
% 47.46/6.48  bmc1_unsat_core_parents_size:           -1
% 47.46/6.48  bmc1_merge_next_fun:                    0
% 47.46/6.48  bmc1_unsat_core_clauses_time:           0.
% 47.46/6.48  
% 47.46/6.48  ------ Instantiation
% 47.46/6.48  
% 47.46/6.48  inst_num_of_clauses:                    5396
% 47.46/6.48  inst_num_in_passive:                    1988
% 47.46/6.48  inst_num_in_active:                     4129
% 47.46/6.48  inst_num_in_unprocessed:                1288
% 47.46/6.48  inst_num_of_loops:                      5779
% 47.46/6.48  inst_num_of_learning_restarts:          1
% 47.46/6.48  inst_num_moves_active_passive:          1635
% 47.46/6.48  inst_lit_activity:                      0
% 47.46/6.48  inst_lit_activity_moves:                0
% 47.46/6.48  inst_num_tautologies:                   0
% 47.46/6.48  inst_num_prop_implied:                  0
% 47.46/6.48  inst_num_existing_simplified:           0
% 47.46/6.48  inst_num_eq_res_simplified:             0
% 47.46/6.48  inst_num_child_elim:                    0
% 47.46/6.48  inst_num_of_dismatching_blockings:      6909
% 47.46/6.48  inst_num_of_non_proper_insts:           10413
% 47.46/6.48  inst_num_of_duplicates:                 0
% 47.46/6.48  inst_inst_num_from_inst_to_res:         0
% 47.46/6.48  inst_dismatching_checking_time:         0.
% 47.46/6.48  
% 47.46/6.48  ------ Resolution
% 47.46/6.48  
% 47.46/6.48  res_num_of_clauses:                     71
% 47.46/6.48  res_num_in_passive:                     71
% 47.46/6.48  res_num_in_active:                      0
% 47.46/6.48  res_num_of_loops:                       259
% 47.46/6.48  res_forward_subset_subsumed:            602
% 47.46/6.48  res_backward_subset_subsumed:           68
% 47.46/6.48  res_forward_subsumed:                   0
% 47.46/6.48  res_backward_subsumed:                  0
% 47.46/6.48  res_forward_subsumption_resolution:     3
% 47.46/6.48  res_backward_subsumption_resolution:    0
% 47.46/6.48  res_clause_to_clause_subsumption:       84666
% 47.46/6.48  res_orphan_elimination:                 0
% 47.46/6.48  res_tautology_del:                      1118
% 47.46/6.48  res_num_eq_res_simplified:              0
% 47.46/6.48  res_num_sel_changes:                    0
% 47.46/6.48  res_moves_from_active_to_pass:          0
% 47.46/6.48  
% 47.46/6.48  ------ Superposition
% 47.46/6.48  
% 47.46/6.48  sup_time_total:                         0.
% 47.46/6.48  sup_time_generating:                    0.
% 47.46/6.48  sup_time_sim_full:                      0.
% 47.46/6.48  sup_time_sim_immed:                     0.
% 47.46/6.48  
% 47.46/6.48  sup_num_of_clauses:                     5350
% 47.46/6.48  sup_num_in_active:                      983
% 47.46/6.48  sup_num_in_passive:                     4367
% 47.46/6.48  sup_num_of_loops:                       1155
% 47.46/6.48  sup_fw_superposition:                   7933
% 47.46/6.48  sup_bw_superposition:                   3814
% 47.46/6.48  sup_immediate_simplified:               3719
% 47.46/6.48  sup_given_eliminated:                   87
% 47.46/6.48  comparisons_done:                       0
% 47.46/6.48  comparisons_avoided:                    38
% 47.46/6.48  
% 47.46/6.48  ------ Simplifications
% 47.46/6.48  
% 47.46/6.48  
% 47.46/6.48  sim_fw_subset_subsumed:                 2284
% 47.46/6.48  sim_bw_subset_subsumed:                 82
% 47.46/6.48  sim_fw_subsumed:                        410
% 47.46/6.48  sim_bw_subsumed:                        321
% 47.46/6.48  sim_fw_subsumption_res:                 0
% 47.46/6.48  sim_bw_subsumption_res:                 0
% 47.46/6.48  sim_tautology_del:                      901
% 47.46/6.48  sim_eq_tautology_del:                   36
% 47.46/6.48  sim_eq_res_simp:                        0
% 47.46/6.48  sim_fw_demodulated:                     1086
% 47.46/6.48  sim_bw_demodulated:                     5
% 47.46/6.48  sim_light_normalised:                   56
% 47.46/6.48  sim_joinable_taut:                      0
% 47.46/6.48  sim_joinable_simp:                      0
% 47.46/6.48  sim_ac_normalised:                      0
% 47.46/6.48  sim_smt_subsumption:                    0
% 47.46/6.48  
%------------------------------------------------------------------------------
