%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1053+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:47 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 671 expanded)
%              Number of clauses        :   80 ( 177 expanded)
%              Number of leaves         :   14 ( 180 expanded)
%              Depth                    :   23
%              Number of atoms          :  555 (2909 expanded)
%              Number of equality atoms :  173 ( 676 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k9_setfam_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f43,f33])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
     => ? [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X0)
             => k1_funct_1(X1,X3) = k11_relat_1(X2,X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
          & v1_funct_2(X1,X0,k9_setfam_1(X0))
          & v1_funct_1(X1) )
       => ? [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k1_funct_1(X1,X3) = k11_relat_1(X2,X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      & v1_funct_2(X1,X0,k9_setfam_1(X0))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      & v1_funct_2(X1,X0,k9_setfam_1(X0))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k1_funct_1(X1,sK4(X2)) != k11_relat_1(X2,sK4(X2))
        & r2_hidden(sK4(X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( k1_funct_1(X1,X3) != k11_relat_1(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(sK3,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,sK2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2))))
      & v1_funct_2(sK3,sK2,k9_setfam_1(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ! [X2] :
        ( ( k1_funct_1(sK3,sK4(X2)) != k11_relat_1(X2,sK4(X2))
          & r2_hidden(sK4(X2),sK2) )
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2))))
    & v1_funct_2(sK3,sK2,k9_setfam_1(sK2))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f28,f27])).

fof(f45,plain,(
    v1_funct_2(sK3,sK2,k9_setfam_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    m1_subset_1(sK3,k9_setfam_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2)))) ),
    inference(definition_unfolding,[],[f46,f33])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( r2_hidden(X2,k2_subset_1(X0))
             => r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0)) ) )
       => ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,k2_subset_1(X0))
                 => k1_funct_1(X1,X3) = k11_relat_1(X2,X3) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( r2_hidden(X2,k2_subset_1(X0))
             => r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0)) ) )
       => ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ( r2_hidden(X4,k2_subset_1(X0))
                 => k1_funct_1(X1,X4) = k11_relat_1(X3,X4) ) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X1,X4) = k11_relat_1(X3,X4)
              | ~ r2_hidden(X4,k2_subset_1(X0))
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ? [X2] :
          ( ~ r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0))
          & r2_hidden(X2,k2_subset_1(X0))
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X1,X4) = k11_relat_1(X3,X4)
              | ~ r2_hidden(X4,k2_subset_1(X0))
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ? [X2] :
          ( ~ r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0))
          & r2_hidden(X2,k2_subset_1(X0))
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,k2_subset_1(X0))
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ? [X4] :
          ( ~ r1_tarski(k1_funct_1(X1,X4),k2_subset_1(X0))
          & r2_hidden(X4,k2_subset_1(X0))
          & m1_subset_1(X4,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(rectify,[],[f15])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ~ r1_tarski(k1_funct_1(X1,X4),k2_subset_1(X0))
          & r2_hidden(X4,k2_subset_1(X0))
          & m1_subset_1(X4,X0) )
     => ( ~ r1_tarski(k1_funct_1(X1,sK1(X0,X1)),k2_subset_1(X0))
        & r2_hidden(sK1(X0,X1),k2_subset_1(X0))
        & m1_subset_1(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,k2_subset_1(X0))
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
     => ( ! [X3] :
            ( k1_funct_1(X1,X3) = k11_relat_1(sK0(X0,X1),X3)
            | ~ r2_hidden(X3,k2_subset_1(X0))
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( k1_funct_1(X1,X3) = k11_relat_1(sK0(X0,X1),X3)
            | ~ r2_hidden(X3,k2_subset_1(X0))
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ( ~ r1_tarski(k1_funct_1(X1,sK1(X0,X1)),k2_subset_1(X0))
        & r2_hidden(sK1(X0,X1),k2_subset_1(X0))
        & m1_subset_1(sK1(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | ~ r1_tarski(k1_funct_1(X1,sK1(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | ~ r1_tarski(k1_funct_1(X1,sK1(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_unfolding,[],[f36,f33,f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f41,f33])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | r2_hidden(sK1(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | r2_hidden(sK1(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_unfolding,[],[f35,f33,f33])).

fof(f47,plain,(
    ! [X2] :
      ( r2_hidden(sK4(X2),sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X2] :
      ( r2_hidden(sK4(X2),sK2)
      | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(definition_unfolding,[],[f47,f33])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | r2_hidden(sK1(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | r2_hidden(sK1(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | ~ r1_tarski(k1_funct_1(X1,sK1(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | ~ r1_tarski(k1_funct_1(X1,sK1(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_unfolding,[],[f39,f33])).

fof(f48,plain,(
    ! [X2] :
      ( k1_funct_1(sK3,sK4(X2)) != k11_relat_1(X2,sK4(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X2] :
      ( k1_funct_1(sK3,sK4(X2)) != k11_relat_1(X2,sK4(X2))
      | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(definition_unfolding,[],[f48,f33])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK3,sK2,k9_setfam_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k9_setfam_1(sK2) != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_406,plain,
    ( ~ m1_subset_1(sK3,k9_setfam_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2))))
    | ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK3,X0),k9_setfam_1(sK2))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = k9_setfam_1(sK2) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k9_setfam_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_410,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k9_setfam_1(sK2))
    | ~ r2_hidden(X0,sK2)
    | k1_xboole_0 = k9_setfam_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_17,c_15])).

cnf(c_411,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK3,X0),k9_setfam_1(sK2))
    | k1_xboole_0 = k9_setfam_1(sK2) ),
    inference(renaming,[status(thm)],[c_410])).

cnf(c_777,plain,
    ( k1_xboole_0 = k9_setfam_1(sK2)
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k9_setfam_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_1,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_204,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_205,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_803,plain,
    ( k9_setfam_1(sK2) = o_0_0_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k9_setfam_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_777,c_205])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_199,plain,
    ( k9_setfam_1(X0) != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_807,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k9_setfam_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_803,c_199])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_781,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1156,plain,
    ( m1_subset_1(k1_funct_1(sK3,X0),k9_setfam_1(sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_781])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,k9_setfam_1(X1))
    | ~ r1_tarski(k1_funct_1(X0,sK1(X1,X0)),k2_subset_1(X1))
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | m1_subset_1(sK0(X1,X0),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_211,plain,
    ( ~ v1_funct_2(X0,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,k9_setfam_1(X3))
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | m1_subset_1(sK0(X1,X0),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(X1,X0)) != X2
    | k2_subset_1(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_212,plain,
    ( ~ v1_funct_2(X0,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | m1_subset_1(sK0(X1,X0),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | ~ m1_subset_1(k1_funct_1(X0,sK1(X1,X0)),k9_setfam_1(k2_subset_1(X1)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | m1_subset_1(sK0(X1,X0),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | ~ m1_subset_1(k1_funct_1(X0,sK1(X1,X0)),k9_setfam_1(k2_subset_1(X1)))
    | ~ v1_funct_1(X0)
    | k9_setfam_1(X1) != k9_setfam_1(sK2)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_16])).

cnf(c_301,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(k2_subset_1(sK2),k2_subset_1(sK2))))
    | ~ m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(k2_subset_1(sK2)))
    | ~ m1_subset_1(sK3,k9_setfam_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2))))
    | ~ v1_funct_1(sK3)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_303,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(k2_subset_1(sK2),k2_subset_1(sK2))))
    | ~ m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(k2_subset_1(sK2)))
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_17,c_15])).

cnf(c_484,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(k2_subset_1(sK2),k2_subset_1(sK2))))
    | ~ m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(k2_subset_1(sK2))) ),
    inference(equality_resolution_simp,[status(thm)],[c_303])).

cnf(c_772,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(k2_subset_1(sK2),k2_subset_1(sK2)))) = iProver_top
    | m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(k2_subset_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_819,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
    | m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_772,c_0])).

cnf(c_1200,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
    | r2_hidden(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_819])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | m1_subset_1(sK0(X1,X0),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | r2_hidden(sK1(X1,X0),k2_subset_1(X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | m1_subset_1(sK0(X1,X0),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | r2_hidden(sK1(X1,X0),k2_subset_1(X1))
    | ~ v1_funct_1(X0)
    | k9_setfam_1(X1) != k9_setfam_1(sK2)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_335,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(k2_subset_1(sK2),k2_subset_1(sK2))))
    | ~ m1_subset_1(sK3,k9_setfam_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2))))
    | r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2))
    | ~ v1_funct_1(sK3)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_337,plain,
    ( r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2))
    | m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(k2_subset_1(sK2),k2_subset_1(sK2))))
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_17,c_15])).

cnf(c_338,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(k2_subset_1(sK2),k2_subset_1(sK2))))
    | r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2))
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_480,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(k2_subset_1(sK2),k2_subset_1(sK2))))
    | r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_338])).

cnf(c_774,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(k2_subset_1(sK2),k2_subset_1(sK2)))) = iProver_top
    | r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_814,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
    | r2_hidden(sK1(sK2,sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_774,c_0])).

cnf(c_1304,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1200,c_814])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(sK2,sK2)))
    | r2_hidden(sK4(X0),sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_779,plain,
    ( m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r2_hidden(sK4(X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1309,plain,
    ( r2_hidden(sK4(sK0(sK2,sK3)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1304,c_779])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | m1_subset_1(sK1(X1,X0),X1)
    | ~ r2_hidden(X2,k2_subset_1(X1))
    | ~ v1_funct_1(X0)
    | k11_relat_1(sK0(X1,X0),X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | m1_subset_1(sK1(X1,X2),X1)
    | ~ r2_hidden(X0,k2_subset_1(X1))
    | ~ v1_funct_1(X2)
    | k11_relat_1(sK0(X1,X2),X0) = k1_funct_1(X2,X0)
    | k9_setfam_1(X1) != k9_setfam_1(sK2)
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK1(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k9_setfam_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2))))
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | ~ v1_funct_1(sK3)
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,k2_subset_1(sK2))
    | ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK1(sK2,sK3),sK2)
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_17,c_15])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK1(sK2,sK3),sK2)
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(renaming,[status(thm)],[c_356])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK1(sK2,sK3),sK2)
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_357])).

cnf(c_775,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK3),sK2) = iProver_top
    | r2_hidden(X0,k2_subset_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_824,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK3),sK2) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_775,c_0])).

cnf(c_829,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(sK1(sK2,sK3),sK2) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_824,c_781])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | ~ r2_hidden(X2,k2_subset_1(X1))
    | r2_hidden(sK1(X1,X0),k2_subset_1(X1))
    | ~ v1_funct_1(X0)
    | k11_relat_1(sK0(X1,X0),X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | ~ r2_hidden(X0,k2_subset_1(X1))
    | r2_hidden(sK1(X1,X2),k2_subset_1(X1))
    | ~ v1_funct_1(X2)
    | k11_relat_1(sK0(X1,X2),X0) = k1_funct_1(X2,X0)
    | k9_setfam_1(X1) != k9_setfam_1(sK2)
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(sK3,k9_setfam_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2))))
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2))
    | ~ v1_funct_1(sK3)
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_383,plain,
    ( r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2))
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | ~ m1_subset_1(X0,sK2)
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_17,c_15])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2))
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(renaming,[status(thm)],[c_383])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2))
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_384])).

cnf(c_776,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,k2_subset_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3),k2_subset_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_833,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK2,sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_776,c_0])).

cnf(c_838,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK2,sK3),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_833,c_781])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,k9_setfam_1(X1))
    | ~ r1_tarski(k1_funct_1(X0,sK1(X1,X0)),k2_subset_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | ~ r2_hidden(X2,k2_subset_1(X1))
    | ~ v1_funct_1(X0)
    | k11_relat_1(sK0(X1,X0),X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_232,plain,
    ( ~ v1_funct_2(X0,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,k9_setfam_1(X4))
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | ~ r2_hidden(X2,k2_subset_1(X1))
    | ~ v1_funct_1(X0)
    | k11_relat_1(sK0(X1,X0),X2) = k1_funct_1(X0,X2)
    | k1_funct_1(X0,sK1(X1,X0)) != X3
    | k2_subset_1(X1) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_233,plain,
    ( ~ v1_funct_2(X0,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | ~ m1_subset_1(k1_funct_1(X0,sK1(X1,X0)),k9_setfam_1(k2_subset_1(X1)))
    | ~ r2_hidden(X2,k2_subset_1(X1))
    | ~ v1_funct_1(X0)
    | k11_relat_1(sK0(X1,X0),X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | ~ m1_subset_1(k1_funct_1(X2,sK1(X1,X2)),k9_setfam_1(k2_subset_1(X1)))
    | ~ r2_hidden(X0,k2_subset_1(X1))
    | ~ v1_funct_1(X2)
    | k11_relat_1(sK0(X1,X2),X0) = k1_funct_1(X2,X0)
    | k9_setfam_1(X1) != k9_setfam_1(sK2)
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_16])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(k2_subset_1(sK2)))
    | ~ m1_subset_1(sK3,k9_setfam_1(k2_zfmisc_1(sK2,k9_setfam_1(sK2))))
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | ~ v1_funct_1(sK3)
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_278,plain,
    ( ~ r2_hidden(X0,k2_subset_1(sK2))
    | ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(k2_subset_1(sK2)))
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_17,c_15])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(k2_subset_1(sK2)))
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | k9_setfam_1(sK2) != k9_setfam_1(sK2) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(k2_subset_1(sK2)))
    | ~ r2_hidden(X0,k2_subset_1(sK2))
    | k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_279])).

cnf(c_771,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(k2_subset_1(sK2))) != iProver_top
    | r2_hidden(X0,k2_subset_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_842,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(sK2)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_771,c_0])).

cnf(c_847,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(k1_funct_1(sK3,sK1(sK2,sK3)),k9_setfam_1(sK2)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_842,c_781])).

cnf(c_1372,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_847])).

cnf(c_1442,plain,
    ( k11_relat_1(sK0(sK2,sK3),X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_829,c_838,c_1372])).

cnf(c_1450,plain,
    ( k11_relat_1(sK0(sK2,sK3),sK4(sK0(sK2,sK3))) = k1_funct_1(sK3,sK4(sK0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_1309,c_1442])).

cnf(c_13,negated_conjecture,
    ( ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(sK2,sK2)))
    | k1_funct_1(sK3,sK4(X0)) != k11_relat_1(X0,sK4(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_780,plain,
    ( k1_funct_1(sK3,sK4(X0)) != k11_relat_1(X0,sK4(X0))
    | m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1464,plain,
    ( m1_subset_1(sK0(sK2,sK3),k9_setfam_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_780])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1464,c_1304])).


%------------------------------------------------------------------------------
