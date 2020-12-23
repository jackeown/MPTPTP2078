%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:38 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :  170 (3764 expanded)
%              Number of clauses        :   97 ( 855 expanded)
%              Number of leaves         :   18 ( 952 expanded)
%              Depth                    :   34
%              Number of atoms          :  472 (18748 expanded)
%              Number of equality atoms :  460 (18659 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f88])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f89])).

fof(f222,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f140])).

fof(f45,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f45])).

fof(f68,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f69,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f68])).

fof(f95,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK6 != sK10
        | sK5 != sK9
        | sK4 != sK8
        | sK3 != sK7 )
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k4_zfmisc_1(sK3,sK4,sK5,sK6) = k4_zfmisc_1(sK7,sK8,sK9,sK10) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,
    ( ( sK6 != sK10
      | sK5 != sK9
      | sK4 != sK8
      | sK3 != sK7 )
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k4_zfmisc_1(sK3,sK4,sK5,sK6) = k4_zfmisc_1(sK7,sK8,sK9,sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f69,f95])).

fof(f177,plain,(
    k4_zfmisc_1(sK3,sK4,sK5,sK6) = k4_zfmisc_1(sK7,sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f96])).

fof(f43,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f171,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f43])).

fof(f218,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10) ),
    inference(definition_unfolding,[],[f177,f171,f171])).

fof(f41,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f65])).

fof(f165,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f38,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f157,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f38])).

fof(f209,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f165,f157,f157,f157])).

fof(f178,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f96])).

fof(f179,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f96])).

fof(f180,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f96])).

fof(f181,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f96])).

fof(f44,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f94,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f93])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f94])).

fof(f217,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f172,f171])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f144,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f143,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f63])).

fof(f164,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f204,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f164,f157,f157])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f216,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f173,f171])).

fof(f230,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f216])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f35])).

fof(f153,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f34,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f151,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f89])).

fof(f223,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f139])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f126,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f186,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f98,f126,f126])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f33,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f150,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f125,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f16,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f124,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

fof(f195,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f124,f126])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f167,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f207,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f167,f157,f157,f157])).

fof(f182,plain,
    ( sK6 != sK10
    | sK5 != sK9
    | sK4 != sK8
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f96])).

fof(f163,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f205,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f163,f157,f157])).

fof(f166,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f208,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f166,f157,f157,f157])).

cnf(c_38,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f222])).

cnf(c_80,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10) ),
    inference(cnf_transformation,[],[f218])).

cnf(c_66,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f209])).

cnf(c_5029,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK7,sK8) = X0 ),
    inference(superposition,[status(thm)],[c_80,c_66])).

cnf(c_79,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f178])).

cnf(c_78,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f179])).

cnf(c_77,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f180])).

cnf(c_76,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f181])).

cnf(c_5034,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK7,sK8) = X0 ),
    inference(superposition,[status(thm)],[c_80,c_66])).

cnf(c_5043,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = X0 ),
    inference(demodulation,[status(thm)],[c_5034,c_80])).

cnf(c_74,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f217])).

cnf(c_2326,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,X0),X1),X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_3306,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),X0),X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_2326])).

cnf(c_4116,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_3306])).

cnf(c_5793,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_4116])).

cnf(c_5817,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK7,sK8) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5029,c_79,c_78,c_77,c_76,c_5043,c_5793])).

cnf(c_5825,plain,
    ( k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK3,sK4) ),
    inference(equality_resolution,[status(thm)],[c_5817])).

cnf(c_43,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_8214,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK7,X0),k2_zfmisc_1(sK3,sK4)) = k2_zfmisc_1(sK7,k4_xboole_0(X0,sK8)) ),
    inference(superposition,[status(thm)],[c_5825,c_43])).

cnf(c_44,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_11728,plain,
    ( k2_zfmisc_1(sK7,k4_xboole_0(sK4,sK8)) = k2_zfmisc_1(k4_xboole_0(sK7,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_8214,c_44])).

cnf(c_61,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X5
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f204])).

cnf(c_5554,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X1) != k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_80,c_61])).

cnf(c_12050,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X0) != k2_zfmisc_1(k2_zfmisc_1(sK7,k4_xboole_0(sK4,sK8)),X1)
    | k4_xboole_0(sK7,sK3) = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_11728,c_5554])).

cnf(c_81,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_73,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f230])).

cnf(c_82,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_1131,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2311,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_2312,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2311])).

cnf(c_12333,plain,
    ( k4_xboole_0(sK7,sK3) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X0) != k2_zfmisc_1(k2_zfmisc_1(sK7,k4_xboole_0(sK4,sK8)),X1)
    | X0 = X1
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12050,c_78,c_81,c_82,c_2312])).

cnf(c_12334,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X0) != k2_zfmisc_1(k2_zfmisc_1(sK7,k4_xboole_0(sK4,sK8)),X1)
    | k4_xboole_0(sK7,sK3) = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_12333])).

cnf(c_52,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f153])).

cnf(c_51,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_2135,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_8204,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK3,sK4)),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_5825,c_2135])).

cnf(c_11858,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(sK4,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_52,c_8204])).

cnf(c_2346,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_2347,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_12286,plain,
    ( r1_tarski(sK4,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11858,c_79,c_78,c_81,c_82,c_2312,c_2347])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2161,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12291,plain,
    ( k4_xboole_0(sK4,sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12286,c_2161])).

cnf(c_12335,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X1) != k2_zfmisc_1(k2_zfmisc_1(sK7,k1_xboole_0),X0)
    | k4_xboole_0(sK7,sK3) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(light_normalisation,[status(thm)],[c_12334,c_12291])).

cnf(c_39,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f223])).

cnf(c_12336,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X0) != k1_xboole_0
    | k4_xboole_0(sK7,sK3) = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(demodulation,[status(thm)],[c_12335,c_38,c_39])).

cnf(c_12337,plain,
    ( k4_xboole_0(sK7,sK3) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_38,c_12336])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f186])).

cnf(c_12985,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK7)) = k4_xboole_0(sK7,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_12337,c_3])).

cnf(c_53,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f152])).

cnf(c_50,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_2136,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_8202,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,sK4)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5825,c_2136])).

cnf(c_11812,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(sK3,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_53,c_8202])).

cnf(c_12278,plain,
    ( r1_tarski(sK3,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11812,c_79,c_78,c_81,c_82,c_2312,c_2347])).

cnf(c_12283,plain,
    ( k4_xboole_0(sK3,sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12278,c_2161])).

cnf(c_13003,plain,
    ( k4_xboole_0(sK7,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(light_normalisation,[status(thm)],[c_12985,c_12283])).

cnf(c_28,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_13004,plain,
    ( sK7 = sK3
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_13003,c_28])).

cnf(c_13561,plain,
    ( sK7 = sK3 ),
    inference(superposition,[status(thm)],[c_13004,c_76])).

cnf(c_13753,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,sK4)) = k2_zfmisc_1(sK3,k4_xboole_0(X0,sK8)) ),
    inference(demodulation,[status(thm)],[c_13561,c_8214])).

cnf(c_13764,plain,
    ( k2_zfmisc_1(sK3,k4_xboole_0(X0,sK8)) = k2_zfmisc_1(sK3,k4_xboole_0(X0,sK4)) ),
    inference(demodulation,[status(thm)],[c_13753,c_43])).

cnf(c_8209,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK7,X0)) = k2_zfmisc_1(sK7,k4_xboole_0(sK8,X0)) ),
    inference(superposition,[status(thm)],[c_5825,c_43])).

cnf(c_13755,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,X0)) = k2_zfmisc_1(sK3,k4_xboole_0(sK8,X0)) ),
    inference(demodulation,[status(thm)],[c_13561,c_8209])).

cnf(c_13761,plain,
    ( k2_zfmisc_1(sK3,k4_xboole_0(sK8,X0)) = k2_zfmisc_1(sK3,k4_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_13755,c_43])).

cnf(c_14386,plain,
    ( k2_zfmisc_1(sK3,k4_xboole_0(sK8,sK4)) = k2_zfmisc_1(sK3,k4_xboole_0(sK4,sK8)) ),
    inference(superposition,[status(thm)],[c_13764,c_13761])).

cnf(c_14389,plain,
    ( k2_zfmisc_1(sK3,k4_xboole_0(sK8,sK4)) = k2_zfmisc_1(sK3,k4_xboole_0(sK4,sK4)) ),
    inference(demodulation,[status(thm)],[c_14386,c_13764])).

cnf(c_27,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f195])).

cnf(c_2177,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_27,c_28])).

cnf(c_14390,plain,
    ( k2_zfmisc_1(sK3,k4_xboole_0(sK8,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14389,c_38,c_2177,c_13761])).

cnf(c_40,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_14610,plain,
    ( k4_xboole_0(sK8,sK4) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14390,c_40])).

cnf(c_14722,plain,
    ( k4_xboole_0(sK8,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14610,c_79,c_81,c_82,c_2347])).

cnf(c_14741,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK8)) = k4_xboole_0(sK8,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14722,c_3])).

cnf(c_14748,plain,
    ( k4_xboole_0(sK8,k1_xboole_0) = k4_xboole_0(sK4,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_14741,c_12291])).

cnf(c_14749,plain,
    ( sK8 = sK4 ),
    inference(demodulation,[status(thm)],[c_14748,c_28])).

cnf(c_5551,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK10 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_80,c_61])).

cnf(c_64,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f207])).

cnf(c_4900,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK10 = X2 ),
    inference(superposition,[status(thm)],[c_80,c_64])).

cnf(c_4908,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k1_xboole_0
    | sK10 = X2 ),
    inference(demodulation,[status(thm)],[c_4900,c_80])).

cnf(c_6242,plain,
    ( sK10 = X2
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5551,c_79,c_78,c_77,c_76,c_4908,c_5793])).

cnf(c_6243,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK10 = X2 ),
    inference(renaming,[status(thm)],[c_6242])).

cnf(c_6250,plain,
    ( sK10 = sK6 ),
    inference(equality_resolution,[status(thm)],[c_6243])).

cnf(c_75,negated_conjecture,
    ( sK3 != sK7
    | sK4 != sK8
    | sK5 != sK9
    | sK6 != sK10 ),
    inference(cnf_transformation,[],[f182])).

cnf(c_7735,plain,
    ( sK7 != sK3
    | sK8 != sK4
    | sK9 != sK5
    | sK6 != sK6 ),
    inference(demodulation,[status(thm)],[c_6250,c_75])).

cnf(c_7738,plain,
    ( sK7 != sK3
    | sK8 != sK4
    | sK9 != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_7735])).

cnf(c_62,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X1
    | k1_xboole_0 = X5 ),
    inference(cnf_transformation,[],[f205])).

cnf(c_5564,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK9 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_80,c_62])).

cnf(c_65,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f208])).

cnf(c_5013,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK9 = X1 ),
    inference(superposition,[status(thm)],[c_80,c_65])).

cnf(c_5022,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k1_xboole_0
    | sK9 = X1 ),
    inference(demodulation,[status(thm)],[c_5013,c_80])).

cnf(c_6343,plain,
    ( sK9 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5564,c_79,c_78,c_77,c_76,c_5022,c_5793])).

cnf(c_6344,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK9 = X1 ),
    inference(renaming,[status(thm)],[c_6343])).

cnf(c_6351,plain,
    ( sK9 = sK5 ),
    inference(equality_resolution,[status(thm)],[c_6344])).

cnf(c_7739,plain,
    ( sK7 != sK3
    | sK8 != sK4
    | sK5 != sK5 ),
    inference(light_normalisation,[status(thm)],[c_7738,c_6351])).

cnf(c_7740,plain,
    ( sK7 != sK3
    | sK8 != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_7739])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14749,c_13561,c_7740])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:32:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.06/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.06/1.49  
% 7.06/1.49  ------  iProver source info
% 7.06/1.49  
% 7.06/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.06/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.06/1.49  git: non_committed_changes: false
% 7.06/1.49  git: last_make_outside_of_git: false
% 7.06/1.49  
% 7.06/1.49  ------ 
% 7.06/1.49  
% 7.06/1.49  ------ Input Options
% 7.06/1.49  
% 7.06/1.49  --out_options                           all
% 7.06/1.49  --tptp_safe_out                         true
% 7.06/1.49  --problem_path                          ""
% 7.06/1.49  --include_path                          ""
% 7.06/1.49  --clausifier                            res/vclausify_rel
% 7.06/1.49  --clausifier_options                    ""
% 7.06/1.49  --stdin                                 false
% 7.06/1.49  --stats_out                             all
% 7.06/1.49  
% 7.06/1.49  ------ General Options
% 7.06/1.49  
% 7.06/1.49  --fof                                   false
% 7.06/1.49  --time_out_real                         305.
% 7.06/1.49  --time_out_virtual                      -1.
% 7.06/1.49  --symbol_type_check                     false
% 7.06/1.49  --clausify_out                          false
% 7.06/1.49  --sig_cnt_out                           false
% 7.06/1.49  --trig_cnt_out                          false
% 7.06/1.49  --trig_cnt_out_tolerance                1.
% 7.06/1.49  --trig_cnt_out_sk_spl                   false
% 7.06/1.49  --abstr_cl_out                          false
% 7.06/1.49  
% 7.06/1.49  ------ Global Options
% 7.06/1.49  
% 7.06/1.49  --schedule                              default
% 7.06/1.49  --add_important_lit                     false
% 7.06/1.49  --prop_solver_per_cl                    1000
% 7.06/1.49  --min_unsat_core                        false
% 7.06/1.49  --soft_assumptions                      false
% 7.06/1.49  --soft_lemma_size                       3
% 7.06/1.49  --prop_impl_unit_size                   0
% 7.06/1.49  --prop_impl_unit                        []
% 7.06/1.49  --share_sel_clauses                     true
% 7.06/1.49  --reset_solvers                         false
% 7.06/1.49  --bc_imp_inh                            [conj_cone]
% 7.06/1.49  --conj_cone_tolerance                   3.
% 7.06/1.49  --extra_neg_conj                        none
% 7.06/1.49  --large_theory_mode                     true
% 7.06/1.49  --prolific_symb_bound                   200
% 7.06/1.49  --lt_threshold                          2000
% 7.06/1.49  --clause_weak_htbl                      true
% 7.06/1.49  --gc_record_bc_elim                     false
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing Options
% 7.06/1.49  
% 7.06/1.49  --preprocessing_flag                    true
% 7.06/1.49  --time_out_prep_mult                    0.1
% 7.06/1.49  --splitting_mode                        input
% 7.06/1.49  --splitting_grd                         true
% 7.06/1.49  --splitting_cvd                         false
% 7.06/1.49  --splitting_cvd_svl                     false
% 7.06/1.49  --splitting_nvd                         32
% 7.06/1.49  --sub_typing                            true
% 7.06/1.49  --prep_gs_sim                           true
% 7.06/1.49  --prep_unflatten                        true
% 7.06/1.49  --prep_res_sim                          true
% 7.06/1.49  --prep_upred                            true
% 7.06/1.49  --prep_sem_filter                       exhaustive
% 7.06/1.49  --prep_sem_filter_out                   false
% 7.06/1.49  --pred_elim                             true
% 7.06/1.49  --res_sim_input                         true
% 7.06/1.49  --eq_ax_congr_red                       true
% 7.06/1.49  --pure_diseq_elim                       true
% 7.06/1.49  --brand_transform                       false
% 7.06/1.49  --non_eq_to_eq                          false
% 7.06/1.49  --prep_def_merge                        true
% 7.06/1.49  --prep_def_merge_prop_impl              false
% 7.06/1.49  --prep_def_merge_mbd                    true
% 7.06/1.49  --prep_def_merge_tr_red                 false
% 7.06/1.49  --prep_def_merge_tr_cl                  false
% 7.06/1.49  --smt_preprocessing                     true
% 7.06/1.49  --smt_ac_axioms                         fast
% 7.06/1.49  --preprocessed_out                      false
% 7.06/1.49  --preprocessed_stats                    false
% 7.06/1.49  
% 7.06/1.49  ------ Abstraction refinement Options
% 7.06/1.49  
% 7.06/1.49  --abstr_ref                             []
% 7.06/1.49  --abstr_ref_prep                        false
% 7.06/1.49  --abstr_ref_until_sat                   false
% 7.06/1.49  --abstr_ref_sig_restrict                funpre
% 7.06/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.49  --abstr_ref_under                       []
% 7.06/1.49  
% 7.06/1.49  ------ SAT Options
% 7.06/1.49  
% 7.06/1.49  --sat_mode                              false
% 7.06/1.49  --sat_fm_restart_options                ""
% 7.06/1.49  --sat_gr_def                            false
% 7.06/1.49  --sat_epr_types                         true
% 7.06/1.49  --sat_non_cyclic_types                  false
% 7.06/1.49  --sat_finite_models                     false
% 7.06/1.49  --sat_fm_lemmas                         false
% 7.06/1.49  --sat_fm_prep                           false
% 7.06/1.49  --sat_fm_uc_incr                        true
% 7.06/1.49  --sat_out_model                         small
% 7.06/1.49  --sat_out_clauses                       false
% 7.06/1.49  
% 7.06/1.49  ------ QBF Options
% 7.06/1.49  
% 7.06/1.49  --qbf_mode                              false
% 7.06/1.49  --qbf_elim_univ                         false
% 7.06/1.49  --qbf_dom_inst                          none
% 7.06/1.49  --qbf_dom_pre_inst                      false
% 7.06/1.49  --qbf_sk_in                             false
% 7.06/1.49  --qbf_pred_elim                         true
% 7.06/1.49  --qbf_split                             512
% 7.06/1.49  
% 7.06/1.49  ------ BMC1 Options
% 7.06/1.49  
% 7.06/1.49  --bmc1_incremental                      false
% 7.06/1.49  --bmc1_axioms                           reachable_all
% 7.06/1.49  --bmc1_min_bound                        0
% 7.06/1.49  --bmc1_max_bound                        -1
% 7.06/1.49  --bmc1_max_bound_default                -1
% 7.06/1.49  --bmc1_symbol_reachability              true
% 7.06/1.49  --bmc1_property_lemmas                  false
% 7.06/1.49  --bmc1_k_induction                      false
% 7.06/1.49  --bmc1_non_equiv_states                 false
% 7.06/1.49  --bmc1_deadlock                         false
% 7.06/1.49  --bmc1_ucm                              false
% 7.06/1.49  --bmc1_add_unsat_core                   none
% 7.06/1.49  --bmc1_unsat_core_children              false
% 7.06/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.49  --bmc1_out_stat                         full
% 7.06/1.49  --bmc1_ground_init                      false
% 7.06/1.49  --bmc1_pre_inst_next_state              false
% 7.06/1.49  --bmc1_pre_inst_state                   false
% 7.06/1.49  --bmc1_pre_inst_reach_state             false
% 7.06/1.49  --bmc1_out_unsat_core                   false
% 7.06/1.49  --bmc1_aig_witness_out                  false
% 7.06/1.49  --bmc1_verbose                          false
% 7.06/1.49  --bmc1_dump_clauses_tptp                false
% 7.06/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.49  --bmc1_dump_file                        -
% 7.06/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.49  --bmc1_ucm_extend_mode                  1
% 7.06/1.49  --bmc1_ucm_init_mode                    2
% 7.06/1.49  --bmc1_ucm_cone_mode                    none
% 7.06/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.49  --bmc1_ucm_relax_model                  4
% 7.06/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.49  --bmc1_ucm_layered_model                none
% 7.06/1.49  --bmc1_ucm_max_lemma_size               10
% 7.06/1.49  
% 7.06/1.49  ------ AIG Options
% 7.06/1.49  
% 7.06/1.49  --aig_mode                              false
% 7.06/1.49  
% 7.06/1.49  ------ Instantiation Options
% 7.06/1.49  
% 7.06/1.49  --instantiation_flag                    true
% 7.06/1.49  --inst_sos_flag                         true
% 7.06/1.49  --inst_sos_phase                        true
% 7.06/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel_side                     num_symb
% 7.06/1.49  --inst_solver_per_active                1400
% 7.06/1.49  --inst_solver_calls_frac                1.
% 7.06/1.49  --inst_passive_queue_type               priority_queues
% 7.06/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.49  --inst_passive_queues_freq              [25;2]
% 7.06/1.49  --inst_dismatching                      true
% 7.06/1.49  --inst_eager_unprocessed_to_passive     true
% 7.06/1.49  --inst_prop_sim_given                   true
% 7.06/1.49  --inst_prop_sim_new                     false
% 7.06/1.49  --inst_subs_new                         false
% 7.06/1.49  --inst_eq_res_simp                      false
% 7.06/1.49  --inst_subs_given                       false
% 7.06/1.49  --inst_orphan_elimination               true
% 7.06/1.49  --inst_learning_loop_flag               true
% 7.06/1.49  --inst_learning_start                   3000
% 7.06/1.49  --inst_learning_factor                  2
% 7.06/1.49  --inst_start_prop_sim_after_learn       3
% 7.06/1.49  --inst_sel_renew                        solver
% 7.06/1.49  --inst_lit_activity_flag                true
% 7.06/1.49  --inst_restr_to_given                   false
% 7.06/1.49  --inst_activity_threshold               500
% 7.06/1.49  --inst_out_proof                        true
% 7.06/1.49  
% 7.06/1.49  ------ Resolution Options
% 7.06/1.49  
% 7.06/1.49  --resolution_flag                       true
% 7.06/1.49  --res_lit_sel                           adaptive
% 7.06/1.49  --res_lit_sel_side                      none
% 7.06/1.49  --res_ordering                          kbo
% 7.06/1.49  --res_to_prop_solver                    active
% 7.06/1.49  --res_prop_simpl_new                    false
% 7.06/1.49  --res_prop_simpl_given                  true
% 7.06/1.49  --res_passive_queue_type                priority_queues
% 7.06/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.49  --res_passive_queues_freq               [15;5]
% 7.06/1.49  --res_forward_subs                      full
% 7.06/1.49  --res_backward_subs                     full
% 7.06/1.49  --res_forward_subs_resolution           true
% 7.06/1.49  --res_backward_subs_resolution          true
% 7.06/1.49  --res_orphan_elimination                true
% 7.06/1.49  --res_time_limit                        2.
% 7.06/1.49  --res_out_proof                         true
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Options
% 7.06/1.49  
% 7.06/1.49  --superposition_flag                    true
% 7.06/1.49  --sup_passive_queue_type                priority_queues
% 7.06/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.49  --demod_completeness_check              fast
% 7.06/1.49  --demod_use_ground                      true
% 7.06/1.49  --sup_to_prop_solver                    passive
% 7.06/1.49  --sup_prop_simpl_new                    true
% 7.06/1.49  --sup_prop_simpl_given                  true
% 7.06/1.49  --sup_fun_splitting                     true
% 7.06/1.49  --sup_smt_interval                      50000
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Simplification Setup
% 7.06/1.49  
% 7.06/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.06/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.06/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.06/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.06/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.06/1.49  --sup_immed_triv                        [TrivRules]
% 7.06/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_immed_bw_main                     []
% 7.06/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.06/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_input_bw                          []
% 7.06/1.49  
% 7.06/1.49  ------ Combination Options
% 7.06/1.49  
% 7.06/1.49  --comb_res_mult                         3
% 7.06/1.49  --comb_sup_mult                         2
% 7.06/1.49  --comb_inst_mult                        10
% 7.06/1.49  
% 7.06/1.49  ------ Debug Options
% 7.06/1.49  
% 7.06/1.49  --dbg_backtrace                         false
% 7.06/1.49  --dbg_dump_prop_clauses                 false
% 7.06/1.49  --dbg_dump_prop_clauses_file            -
% 7.06/1.49  --dbg_out_stat                          false
% 7.06/1.49  ------ Parsing...
% 7.06/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.06/1.49  ------ Proving...
% 7.06/1.49  ------ Problem Properties 
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  clauses                                 80
% 7.06/1.49  conjectures                             6
% 7.06/1.49  EPR                                     14
% 7.06/1.49  Horn                                    58
% 7.06/1.49  unary                                   29
% 7.06/1.49  binary                                  30
% 7.06/1.49  lits                                    162
% 7.06/1.49  lits eq                                 87
% 7.06/1.49  fd_pure                                 0
% 7.06/1.49  fd_pseudo                               0
% 7.06/1.49  fd_cond                                 7
% 7.06/1.49  fd_pseudo_cond                          7
% 7.06/1.49  AC symbols                              0
% 7.06/1.49  
% 7.06/1.49  ------ Schedule dynamic 5 is on 
% 7.06/1.49  
% 7.06/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  ------ 
% 7.06/1.49  Current options:
% 7.06/1.49  ------ 
% 7.06/1.49  
% 7.06/1.49  ------ Input Options
% 7.06/1.49  
% 7.06/1.49  --out_options                           all
% 7.06/1.49  --tptp_safe_out                         true
% 7.06/1.49  --problem_path                          ""
% 7.06/1.49  --include_path                          ""
% 7.06/1.49  --clausifier                            res/vclausify_rel
% 7.06/1.49  --clausifier_options                    ""
% 7.06/1.49  --stdin                                 false
% 7.06/1.49  --stats_out                             all
% 7.06/1.49  
% 7.06/1.49  ------ General Options
% 7.06/1.49  
% 7.06/1.49  --fof                                   false
% 7.06/1.49  --time_out_real                         305.
% 7.06/1.49  --time_out_virtual                      -1.
% 7.06/1.49  --symbol_type_check                     false
% 7.06/1.49  --clausify_out                          false
% 7.06/1.49  --sig_cnt_out                           false
% 7.06/1.49  --trig_cnt_out                          false
% 7.06/1.49  --trig_cnt_out_tolerance                1.
% 7.06/1.49  --trig_cnt_out_sk_spl                   false
% 7.06/1.49  --abstr_cl_out                          false
% 7.06/1.49  
% 7.06/1.49  ------ Global Options
% 7.06/1.49  
% 7.06/1.49  --schedule                              default
% 7.06/1.49  --add_important_lit                     false
% 7.06/1.49  --prop_solver_per_cl                    1000
% 7.06/1.49  --min_unsat_core                        false
% 7.06/1.49  --soft_assumptions                      false
% 7.06/1.49  --soft_lemma_size                       3
% 7.06/1.49  --prop_impl_unit_size                   0
% 7.06/1.49  --prop_impl_unit                        []
% 7.06/1.49  --share_sel_clauses                     true
% 7.06/1.49  --reset_solvers                         false
% 7.06/1.49  --bc_imp_inh                            [conj_cone]
% 7.06/1.49  --conj_cone_tolerance                   3.
% 7.06/1.49  --extra_neg_conj                        none
% 7.06/1.49  --large_theory_mode                     true
% 7.06/1.49  --prolific_symb_bound                   200
% 7.06/1.49  --lt_threshold                          2000
% 7.06/1.49  --clause_weak_htbl                      true
% 7.06/1.49  --gc_record_bc_elim                     false
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing Options
% 7.06/1.49  
% 7.06/1.49  --preprocessing_flag                    true
% 7.06/1.49  --time_out_prep_mult                    0.1
% 7.06/1.49  --splitting_mode                        input
% 7.06/1.49  --splitting_grd                         true
% 7.06/1.49  --splitting_cvd                         false
% 7.06/1.49  --splitting_cvd_svl                     false
% 7.06/1.49  --splitting_nvd                         32
% 7.06/1.49  --sub_typing                            true
% 7.06/1.49  --prep_gs_sim                           true
% 7.06/1.49  --prep_unflatten                        true
% 7.06/1.49  --prep_res_sim                          true
% 7.06/1.49  --prep_upred                            true
% 7.06/1.49  --prep_sem_filter                       exhaustive
% 7.06/1.49  --prep_sem_filter_out                   false
% 7.06/1.49  --pred_elim                             true
% 7.06/1.49  --res_sim_input                         true
% 7.06/1.49  --eq_ax_congr_red                       true
% 7.06/1.49  --pure_diseq_elim                       true
% 7.06/1.49  --brand_transform                       false
% 7.06/1.49  --non_eq_to_eq                          false
% 7.06/1.49  --prep_def_merge                        true
% 7.06/1.49  --prep_def_merge_prop_impl              false
% 7.06/1.49  --prep_def_merge_mbd                    true
% 7.06/1.49  --prep_def_merge_tr_red                 false
% 7.06/1.49  --prep_def_merge_tr_cl                  false
% 7.06/1.49  --smt_preprocessing                     true
% 7.06/1.49  --smt_ac_axioms                         fast
% 7.06/1.49  --preprocessed_out                      false
% 7.06/1.49  --preprocessed_stats                    false
% 7.06/1.49  
% 7.06/1.49  ------ Abstraction refinement Options
% 7.06/1.49  
% 7.06/1.49  --abstr_ref                             []
% 7.06/1.49  --abstr_ref_prep                        false
% 7.06/1.49  --abstr_ref_until_sat                   false
% 7.06/1.49  --abstr_ref_sig_restrict                funpre
% 7.06/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.49  --abstr_ref_under                       []
% 7.06/1.49  
% 7.06/1.49  ------ SAT Options
% 7.06/1.49  
% 7.06/1.49  --sat_mode                              false
% 7.06/1.49  --sat_fm_restart_options                ""
% 7.06/1.49  --sat_gr_def                            false
% 7.06/1.49  --sat_epr_types                         true
% 7.06/1.49  --sat_non_cyclic_types                  false
% 7.06/1.49  --sat_finite_models                     false
% 7.06/1.49  --sat_fm_lemmas                         false
% 7.06/1.49  --sat_fm_prep                           false
% 7.06/1.49  --sat_fm_uc_incr                        true
% 7.06/1.49  --sat_out_model                         small
% 7.06/1.49  --sat_out_clauses                       false
% 7.06/1.49  
% 7.06/1.49  ------ QBF Options
% 7.06/1.49  
% 7.06/1.49  --qbf_mode                              false
% 7.06/1.49  --qbf_elim_univ                         false
% 7.06/1.49  --qbf_dom_inst                          none
% 7.06/1.49  --qbf_dom_pre_inst                      false
% 7.06/1.49  --qbf_sk_in                             false
% 7.06/1.49  --qbf_pred_elim                         true
% 7.06/1.49  --qbf_split                             512
% 7.06/1.49  
% 7.06/1.49  ------ BMC1 Options
% 7.06/1.49  
% 7.06/1.49  --bmc1_incremental                      false
% 7.06/1.49  --bmc1_axioms                           reachable_all
% 7.06/1.49  --bmc1_min_bound                        0
% 7.06/1.49  --bmc1_max_bound                        -1
% 7.06/1.49  --bmc1_max_bound_default                -1
% 7.06/1.49  --bmc1_symbol_reachability              true
% 7.06/1.49  --bmc1_property_lemmas                  false
% 7.06/1.49  --bmc1_k_induction                      false
% 7.06/1.49  --bmc1_non_equiv_states                 false
% 7.06/1.49  --bmc1_deadlock                         false
% 7.06/1.49  --bmc1_ucm                              false
% 7.06/1.49  --bmc1_add_unsat_core                   none
% 7.06/1.49  --bmc1_unsat_core_children              false
% 7.06/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.49  --bmc1_out_stat                         full
% 7.06/1.49  --bmc1_ground_init                      false
% 7.06/1.49  --bmc1_pre_inst_next_state              false
% 7.06/1.49  --bmc1_pre_inst_state                   false
% 7.06/1.49  --bmc1_pre_inst_reach_state             false
% 7.06/1.49  --bmc1_out_unsat_core                   false
% 7.06/1.49  --bmc1_aig_witness_out                  false
% 7.06/1.49  --bmc1_verbose                          false
% 7.06/1.49  --bmc1_dump_clauses_tptp                false
% 7.06/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.49  --bmc1_dump_file                        -
% 7.06/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.49  --bmc1_ucm_extend_mode                  1
% 7.06/1.49  --bmc1_ucm_init_mode                    2
% 7.06/1.49  --bmc1_ucm_cone_mode                    none
% 7.06/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.49  --bmc1_ucm_relax_model                  4
% 7.06/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.49  --bmc1_ucm_layered_model                none
% 7.06/1.49  --bmc1_ucm_max_lemma_size               10
% 7.06/1.49  
% 7.06/1.49  ------ AIG Options
% 7.06/1.49  
% 7.06/1.49  --aig_mode                              false
% 7.06/1.49  
% 7.06/1.49  ------ Instantiation Options
% 7.06/1.49  
% 7.06/1.49  --instantiation_flag                    true
% 7.06/1.49  --inst_sos_flag                         true
% 7.06/1.49  --inst_sos_phase                        true
% 7.06/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel_side                     none
% 7.06/1.49  --inst_solver_per_active                1400
% 7.06/1.49  --inst_solver_calls_frac                1.
% 7.06/1.49  --inst_passive_queue_type               priority_queues
% 7.06/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.49  --inst_passive_queues_freq              [25;2]
% 7.06/1.49  --inst_dismatching                      true
% 7.06/1.49  --inst_eager_unprocessed_to_passive     true
% 7.06/1.49  --inst_prop_sim_given                   true
% 7.06/1.49  --inst_prop_sim_new                     false
% 7.06/1.49  --inst_subs_new                         false
% 7.06/1.49  --inst_eq_res_simp                      false
% 7.06/1.49  --inst_subs_given                       false
% 7.06/1.49  --inst_orphan_elimination               true
% 7.06/1.49  --inst_learning_loop_flag               true
% 7.06/1.49  --inst_learning_start                   3000
% 7.06/1.49  --inst_learning_factor                  2
% 7.06/1.49  --inst_start_prop_sim_after_learn       3
% 7.06/1.49  --inst_sel_renew                        solver
% 7.06/1.49  --inst_lit_activity_flag                true
% 7.06/1.49  --inst_restr_to_given                   false
% 7.06/1.49  --inst_activity_threshold               500
% 7.06/1.49  --inst_out_proof                        true
% 7.06/1.49  
% 7.06/1.49  ------ Resolution Options
% 7.06/1.49  
% 7.06/1.49  --resolution_flag                       false
% 7.06/1.49  --res_lit_sel                           adaptive
% 7.06/1.49  --res_lit_sel_side                      none
% 7.06/1.49  --res_ordering                          kbo
% 7.06/1.49  --res_to_prop_solver                    active
% 7.06/1.49  --res_prop_simpl_new                    false
% 7.06/1.49  --res_prop_simpl_given                  true
% 7.06/1.49  --res_passive_queue_type                priority_queues
% 7.06/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.49  --res_passive_queues_freq               [15;5]
% 7.06/1.49  --res_forward_subs                      full
% 7.06/1.49  --res_backward_subs                     full
% 7.06/1.49  --res_forward_subs_resolution           true
% 7.06/1.49  --res_backward_subs_resolution          true
% 7.06/1.49  --res_orphan_elimination                true
% 7.06/1.49  --res_time_limit                        2.
% 7.06/1.49  --res_out_proof                         true
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Options
% 7.06/1.49  
% 7.06/1.49  --superposition_flag                    true
% 7.06/1.49  --sup_passive_queue_type                priority_queues
% 7.06/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.49  --demod_completeness_check              fast
% 7.06/1.49  --demod_use_ground                      true
% 7.06/1.49  --sup_to_prop_solver                    passive
% 7.06/1.49  --sup_prop_simpl_new                    true
% 7.06/1.49  --sup_prop_simpl_given                  true
% 7.06/1.49  --sup_fun_splitting                     true
% 7.06/1.49  --sup_smt_interval                      50000
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Simplification Setup
% 7.06/1.49  
% 7.06/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.06/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.06/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.06/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.06/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.06/1.49  --sup_immed_triv                        [TrivRules]
% 7.06/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_immed_bw_main                     []
% 7.06/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.06/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_input_bw                          []
% 7.06/1.49  
% 7.06/1.49  ------ Combination Options
% 7.06/1.49  
% 7.06/1.49  --comb_res_mult                         3
% 7.06/1.49  --comb_sup_mult                         2
% 7.06/1.49  --comb_inst_mult                        10
% 7.06/1.49  
% 7.06/1.49  ------ Debug Options
% 7.06/1.49  
% 7.06/1.49  --dbg_backtrace                         false
% 7.06/1.49  --dbg_dump_prop_clauses                 false
% 7.06/1.49  --dbg_dump_prop_clauses_file            -
% 7.06/1.49  --dbg_out_stat                          false
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  ------ Proving...
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  % SZS status Theorem for theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  fof(f27,axiom,(
% 7.06/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f88,plain,(
% 7.06/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.06/1.49    inference(nnf_transformation,[],[f27])).
% 7.06/1.49  
% 7.06/1.49  fof(f89,plain,(
% 7.06/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.06/1.49    inference(flattening,[],[f88])).
% 7.06/1.49  
% 7.06/1.49  fof(f140,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.06/1.49    inference(cnf_transformation,[],[f89])).
% 7.06/1.49  
% 7.06/1.49  fof(f222,plain,(
% 7.06/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.06/1.49    inference(equality_resolution,[],[f140])).
% 7.06/1.49  
% 7.06/1.49  fof(f45,conjecture,(
% 7.06/1.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f46,negated_conjecture,(
% 7.06/1.49    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.06/1.49    inference(negated_conjecture,[],[f45])).
% 7.06/1.49  
% 7.06/1.49  fof(f68,plain,(
% 7.06/1.49    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 7.06/1.49    inference(ennf_transformation,[],[f46])).
% 7.06/1.49  
% 7.06/1.49  fof(f69,plain,(
% 7.06/1.49    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 7.06/1.49    inference(flattening,[],[f68])).
% 7.06/1.49  
% 7.06/1.49  fof(f95,plain,(
% 7.06/1.49    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK6 != sK10 | sK5 != sK9 | sK4 != sK8 | sK3 != sK7) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k4_zfmisc_1(sK3,sK4,sK5,sK6) = k4_zfmisc_1(sK7,sK8,sK9,sK10))),
% 7.06/1.49    introduced(choice_axiom,[])).
% 7.06/1.49  
% 7.06/1.49  fof(f96,plain,(
% 7.06/1.49    (sK6 != sK10 | sK5 != sK9 | sK4 != sK8 | sK3 != sK7) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k4_zfmisc_1(sK3,sK4,sK5,sK6) = k4_zfmisc_1(sK7,sK8,sK9,sK10)),
% 7.06/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f69,f95])).
% 7.06/1.49  
% 7.06/1.49  fof(f177,plain,(
% 7.06/1.49    k4_zfmisc_1(sK3,sK4,sK5,sK6) = k4_zfmisc_1(sK7,sK8,sK9,sK10)),
% 7.06/1.49    inference(cnf_transformation,[],[f96])).
% 7.06/1.49  
% 7.06/1.49  fof(f43,axiom,(
% 7.06/1.49    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f171,plain,(
% 7.06/1.49    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f43])).
% 7.06/1.49  
% 7.06/1.49  fof(f218,plain,(
% 7.06/1.49    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10)),
% 7.06/1.49    inference(definition_unfolding,[],[f177,f171,f171])).
% 7.06/1.49  
% 7.06/1.49  fof(f41,axiom,(
% 7.06/1.49    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f65,plain,(
% 7.06/1.49    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 7.06/1.49    inference(ennf_transformation,[],[f41])).
% 7.06/1.49  
% 7.06/1.49  fof(f66,plain,(
% 7.06/1.49    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 7.06/1.49    inference(flattening,[],[f65])).
% 7.06/1.49  
% 7.06/1.49  fof(f165,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f66])).
% 7.06/1.49  
% 7.06/1.49  fof(f38,axiom,(
% 7.06/1.49    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f157,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f38])).
% 7.06/1.49  
% 7.06/1.49  fof(f209,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 7.06/1.49    inference(definition_unfolding,[],[f165,f157,f157,f157])).
% 7.06/1.49  
% 7.06/1.49  fof(f178,plain,(
% 7.06/1.49    k1_xboole_0 != sK3),
% 7.06/1.49    inference(cnf_transformation,[],[f96])).
% 7.06/1.49  
% 7.06/1.49  fof(f179,plain,(
% 7.06/1.49    k1_xboole_0 != sK4),
% 7.06/1.49    inference(cnf_transformation,[],[f96])).
% 7.06/1.49  
% 7.06/1.49  fof(f180,plain,(
% 7.06/1.49    k1_xboole_0 != sK5),
% 7.06/1.49    inference(cnf_transformation,[],[f96])).
% 7.06/1.49  
% 7.06/1.49  fof(f181,plain,(
% 7.06/1.49    k1_xboole_0 != sK6),
% 7.06/1.49    inference(cnf_transformation,[],[f96])).
% 7.06/1.49  
% 7.06/1.49  fof(f44,axiom,(
% 7.06/1.49    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f93,plain,(
% 7.06/1.49    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 7.06/1.49    inference(nnf_transformation,[],[f44])).
% 7.06/1.49  
% 7.06/1.49  fof(f94,plain,(
% 7.06/1.49    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.06/1.49    inference(flattening,[],[f93])).
% 7.06/1.49  
% 7.06/1.49  fof(f172,plain,(
% 7.06/1.49    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.06/1.49    inference(cnf_transformation,[],[f94])).
% 7.06/1.49  
% 7.06/1.49  fof(f217,plain,(
% 7.06/1.49    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.06/1.49    inference(definition_unfolding,[],[f172,f171])).
% 7.06/1.49  
% 7.06/1.49  fof(f29,axiom,(
% 7.06/1.49    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f144,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 7.06/1.49    inference(cnf_transformation,[],[f29])).
% 7.06/1.49  
% 7.06/1.49  fof(f143,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f29])).
% 7.06/1.49  
% 7.06/1.49  fof(f40,axiom,(
% 7.06/1.49    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f63,plain,(
% 7.06/1.49    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 7.06/1.49    inference(ennf_transformation,[],[f40])).
% 7.06/1.49  
% 7.06/1.49  fof(f64,plain,(
% 7.06/1.49    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 7.06/1.49    inference(flattening,[],[f63])).
% 7.06/1.49  
% 7.06/1.49  fof(f164,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f64])).
% 7.06/1.49  
% 7.06/1.49  fof(f204,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 7.06/1.49    inference(definition_unfolding,[],[f164,f157,f157])).
% 7.06/1.49  
% 7.06/1.49  fof(f173,plain,(
% 7.06/1.49    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f94])).
% 7.06/1.49  
% 7.06/1.49  fof(f216,plain,(
% 7.06/1.49    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 7.06/1.49    inference(definition_unfolding,[],[f173,f171])).
% 7.06/1.49  
% 7.06/1.49  fof(f230,plain,(
% 7.06/1.49    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 7.06/1.49    inference(equality_resolution,[],[f216])).
% 7.06/1.49  
% 7.06/1.49  fof(f35,axiom,(
% 7.06/1.49    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f61,plain,(
% 7.06/1.49    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.06/1.49    inference(ennf_transformation,[],[f35])).
% 7.06/1.49  
% 7.06/1.49  fof(f153,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.06/1.49    inference(cnf_transformation,[],[f61])).
% 7.06/1.49  
% 7.06/1.49  fof(f34,axiom,(
% 7.06/1.49    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f151,plain,(
% 7.06/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f34])).
% 7.06/1.49  
% 7.06/1.49  fof(f9,axiom,(
% 7.06/1.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f83,plain,(
% 7.06/1.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.06/1.49    inference(nnf_transformation,[],[f9])).
% 7.06/1.49  
% 7.06/1.49  fof(f114,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f83])).
% 7.06/1.49  
% 7.06/1.49  fof(f139,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.06/1.49    inference(cnf_transformation,[],[f89])).
% 7.06/1.49  
% 7.06/1.49  fof(f223,plain,(
% 7.06/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.06/1.49    inference(equality_resolution,[],[f139])).
% 7.06/1.49  
% 7.06/1.49  fof(f2,axiom,(
% 7.06/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f98,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f2])).
% 7.06/1.49  
% 7.06/1.49  fof(f18,axiom,(
% 7.06/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f126,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.06/1.49    inference(cnf_transformation,[],[f18])).
% 7.06/1.49  
% 7.06/1.49  fof(f186,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.06/1.49    inference(definition_unfolding,[],[f98,f126,f126])).
% 7.06/1.49  
% 7.06/1.49  fof(f152,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.06/1.49    inference(cnf_transformation,[],[f61])).
% 7.06/1.49  
% 7.06/1.49  fof(f33,axiom,(
% 7.06/1.49    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f150,plain,(
% 7.06/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f33])).
% 7.06/1.49  
% 7.06/1.49  fof(f17,axiom,(
% 7.06/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f125,plain,(
% 7.06/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.06/1.49    inference(cnf_transformation,[],[f17])).
% 7.06/1.49  
% 7.06/1.49  fof(f16,axiom,(
% 7.06/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f124,plain,(
% 7.06/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.06/1.49    inference(cnf_transformation,[],[f16])).
% 7.06/1.49  
% 7.06/1.49  fof(f195,plain,(
% 7.06/1.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.06/1.49    inference(definition_unfolding,[],[f124,f126])).
% 7.06/1.49  
% 7.06/1.49  fof(f138,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f89])).
% 7.06/1.49  
% 7.06/1.49  fof(f167,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f66])).
% 7.06/1.49  
% 7.06/1.49  fof(f207,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 7.06/1.49    inference(definition_unfolding,[],[f167,f157,f157,f157])).
% 7.06/1.49  
% 7.06/1.49  fof(f182,plain,(
% 7.06/1.49    sK6 != sK10 | sK5 != sK9 | sK4 != sK8 | sK3 != sK7),
% 7.06/1.49    inference(cnf_transformation,[],[f96])).
% 7.06/1.49  
% 7.06/1.49  fof(f163,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f64])).
% 7.06/1.49  
% 7.06/1.49  fof(f205,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 7.06/1.49    inference(definition_unfolding,[],[f163,f157,f157])).
% 7.06/1.49  
% 7.06/1.49  fof(f166,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f66])).
% 7.06/1.49  
% 7.06/1.49  fof(f208,plain,(
% 7.06/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 7.06/1.49    inference(definition_unfolding,[],[f166,f157,f157,f157])).
% 7.06/1.49  
% 7.06/1.49  cnf(c_38,plain,
% 7.06/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.06/1.49      inference(cnf_transformation,[],[f222]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_80,negated_conjecture,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10) ),
% 7.06/1.49      inference(cnf_transformation,[],[f218]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_66,plain,
% 7.06/1.49      ( X0 = X1
% 7.06/1.49      | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
% 7.06/1.49      | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
% 7.06/1.49      inference(cnf_transformation,[],[f209]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_5029,plain,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 7.06/1.49      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.49      | k2_zfmisc_1(sK7,sK8) = X0 ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_80,c_66]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_79,negated_conjecture,
% 7.06/1.49      ( k1_xboole_0 != sK3 ),
% 7.06/1.49      inference(cnf_transformation,[],[f178]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_78,negated_conjecture,
% 7.06/1.49      ( k1_xboole_0 != sK4 ),
% 7.06/1.49      inference(cnf_transformation,[],[f179]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_77,negated_conjecture,
% 7.06/1.49      ( k1_xboole_0 != sK5 ),
% 7.06/1.49      inference(cnf_transformation,[],[f180]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_76,negated_conjecture,
% 7.06/1.49      ( k1_xboole_0 != sK6 ),
% 7.06/1.49      inference(cnf_transformation,[],[f181]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_5034,plain,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10) = k1_xboole_0
% 7.06/1.49      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.49      | k2_zfmisc_1(sK7,sK8) = X0 ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_80,c_66]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_5043,plain,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.49      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k1_xboole_0
% 7.06/1.49      | k2_zfmisc_1(sK7,sK8) = X0 ),
% 7.06/1.49      inference(demodulation,[status(thm)],[c_5034,c_80]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_74,plain,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 7.06/1.49      | k1_xboole_0 = X0
% 7.06/1.49      | k1_xboole_0 = X1
% 7.06/1.49      | k1_xboole_0 = X2
% 7.06/1.49      | k1_xboole_0 = X3 ),
% 7.06/1.49      inference(cnf_transformation,[],[f217]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_2326,plain,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,X0),X1),X2) != k1_xboole_0
% 7.06/1.49      | k1_xboole_0 = X0
% 7.06/1.49      | k1_xboole_0 = X1
% 7.06/1.49      | k1_xboole_0 = X2
% 7.06/1.49      | k1_xboole_0 = sK3 ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_74]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_3306,plain,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),X0),X1) != k1_xboole_0
% 7.06/1.49      | k1_xboole_0 = X0
% 7.06/1.49      | k1_xboole_0 = X1
% 7.06/1.49      | k1_xboole_0 = sK3
% 7.06/1.49      | k1_xboole_0 = sK4 ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_2326]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_4116,plain,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) != k1_xboole_0
% 7.06/1.49      | k1_xboole_0 = X0
% 7.06/1.49      | k1_xboole_0 = sK3
% 7.06/1.49      | k1_xboole_0 = sK4
% 7.06/1.49      | k1_xboole_0 = sK5 ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_3306]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_5793,plain,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k1_xboole_0
% 7.06/1.49      | k1_xboole_0 = sK3
% 7.06/1.49      | k1_xboole_0 = sK4
% 7.06/1.49      | k1_xboole_0 = sK5
% 7.06/1.49      | k1_xboole_0 = sK6 ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_4116]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_5817,plain,
% 7.06/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.49      | k2_zfmisc_1(sK7,sK8) = X0 ),
% 7.06/1.49      inference(global_propositional_subsumption,
% 7.06/1.49                [status(thm)],
% 7.06/1.49                [c_5029,c_79,c_78,c_77,c_76,c_5043,c_5793]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_5825,plain,
% 7.06/1.49      ( k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK3,sK4) ),
% 7.06/1.49      inference(equality_resolution,[status(thm)],[c_5817]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_43,plain,
% 7.06/1.49      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
% 7.06/1.49      inference(cnf_transformation,[],[f144]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_8214,plain,
% 7.06/1.49      ( k4_xboole_0(k2_zfmisc_1(sK7,X0),k2_zfmisc_1(sK3,sK4)) = k2_zfmisc_1(sK7,k4_xboole_0(X0,sK8)) ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_5825,c_43]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_44,plain,
% 7.06/1.49      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
% 7.06/1.49      inference(cnf_transformation,[],[f143]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_11728,plain,
% 7.06/1.49      ( k2_zfmisc_1(sK7,k4_xboole_0(sK4,sK8)) = k2_zfmisc_1(k4_xboole_0(sK7,sK3),sK4) ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_8214,c_44]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_61,plain,
% 7.06/1.49      ( X0 = X1
% 7.06/1.49      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
% 7.06/1.49      | k1_xboole_0 = X4
% 7.06/1.49      | k1_xboole_0 = X5
% 7.06/1.49      | k1_xboole_0 = X1 ),
% 7.06/1.49      inference(cnf_transformation,[],[f204]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_5554,plain,
% 7.06/1.49      ( X0 = X1
% 7.06/1.49      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X1) != k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0)
% 7.06/1.49      | k1_xboole_0 = X2
% 7.06/1.49      | k1_xboole_0 = X3
% 7.06/1.49      | k1_xboole_0 = X0 ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_80,c_61]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_12050,plain,
% 7.06/1.49      ( X0 = X1
% 7.06/1.49      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X0) != k2_zfmisc_1(k2_zfmisc_1(sK7,k4_xboole_0(sK4,sK8)),X1)
% 7.06/1.49      | k4_xboole_0(sK7,sK3) = k1_xboole_0
% 7.06/1.49      | sK4 = k1_xboole_0
% 7.06/1.49      | k1_xboole_0 = X1 ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_11728,c_5554]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_81,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 7.06/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_74]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_73,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 7.06/1.50      inference(cnf_transformation,[],[f230]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_82,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_73]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_1131,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2311,plain,
% 7.06/1.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_1131]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2312,plain,
% 7.06/1.50      ( sK4 != k1_xboole_0
% 7.06/1.50      | k1_xboole_0 = sK4
% 7.06/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_2311]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12333,plain,
% 7.06/1.50      ( k4_xboole_0(sK7,sK3) = k1_xboole_0
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X0) != k2_zfmisc_1(k2_zfmisc_1(sK7,k4_xboole_0(sK4,sK8)),X1)
% 7.06/1.50      | X0 = X1
% 7.06/1.50      | k1_xboole_0 = X1 ),
% 7.06/1.50      inference(global_propositional_subsumption,
% 7.06/1.50                [status(thm)],
% 7.06/1.50                [c_12050,c_78,c_81,c_82,c_2312]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12334,plain,
% 7.06/1.50      ( X0 = X1
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X0) != k2_zfmisc_1(k2_zfmisc_1(sK7,k4_xboole_0(sK4,sK8)),X1)
% 7.06/1.50      | k4_xboole_0(sK7,sK3) = k1_xboole_0
% 7.06/1.50      | k1_xboole_0 = X1 ),
% 7.06/1.50      inference(renaming,[status(thm)],[c_12333]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_52,plain,
% 7.06/1.50      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 7.06/1.50      | k1_xboole_0 = X0
% 7.06/1.50      | k1_xboole_0 = X1 ),
% 7.06/1.50      inference(cnf_transformation,[],[f153]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_51,plain,
% 7.06/1.50      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
% 7.06/1.50      inference(cnf_transformation,[],[f151]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2135,plain,
% 7.06/1.50      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_8204,plain,
% 7.06/1.50      ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK3,sK4)),sK8) = iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_5825,c_2135]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_11858,plain,
% 7.06/1.50      ( sK3 = k1_xboole_0
% 7.06/1.50      | sK4 = k1_xboole_0
% 7.06/1.50      | r1_tarski(sK4,sK8) = iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_52,c_8204]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2346,plain,
% 7.06/1.50      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_1131]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2347,plain,
% 7.06/1.50      ( sK3 != k1_xboole_0
% 7.06/1.50      | k1_xboole_0 = sK3
% 7.06/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_2346]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12286,plain,
% 7.06/1.50      ( r1_tarski(sK4,sK8) = iProver_top ),
% 7.06/1.50      inference(global_propositional_subsumption,
% 7.06/1.50                [status(thm)],
% 7.06/1.50                [c_11858,c_79,c_78,c_81,c_82,c_2312,c_2347]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_18,plain,
% 7.06/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.06/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2161,plain,
% 7.06/1.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.06/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12291,plain,
% 7.06/1.50      ( k4_xboole_0(sK4,sK8) = k1_xboole_0 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_12286,c_2161]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12335,plain,
% 7.06/1.50      ( X0 = X1
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X1) != k2_zfmisc_1(k2_zfmisc_1(sK7,k1_xboole_0),X0)
% 7.06/1.50      | k4_xboole_0(sK7,sK3) = k1_xboole_0
% 7.06/1.50      | k1_xboole_0 = X0 ),
% 7.06/1.50      inference(light_normalisation,[status(thm)],[c_12334,c_12291]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_39,plain,
% 7.06/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.06/1.50      inference(cnf_transformation,[],[f223]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12336,plain,
% 7.06/1.50      ( X0 = X1
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6),X0) != k1_xboole_0
% 7.06/1.50      | k4_xboole_0(sK7,sK3) = k1_xboole_0
% 7.06/1.50      | k1_xboole_0 = X1 ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_12335,c_38,c_39]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12337,plain,
% 7.06/1.50      ( k4_xboole_0(sK7,sK3) = k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_38,c_12336]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_3,plain,
% 7.06/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.06/1.50      inference(cnf_transformation,[],[f186]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12985,plain,
% 7.06/1.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK7)) = k4_xboole_0(sK7,k1_xboole_0)
% 7.06/1.50      | k1_xboole_0 = X0 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_12337,c_3]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_53,plain,
% 7.06/1.50      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 7.06/1.50      | k1_xboole_0 = X0
% 7.06/1.50      | k1_xboole_0 = X1 ),
% 7.06/1.50      inference(cnf_transformation,[],[f152]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_50,plain,
% 7.06/1.50      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
% 7.06/1.50      inference(cnf_transformation,[],[f150]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2136,plain,
% 7.06/1.50      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_8202,plain,
% 7.06/1.50      ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,sK4)),sK7) = iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_5825,c_2136]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_11812,plain,
% 7.06/1.50      ( sK3 = k1_xboole_0
% 7.06/1.50      | sK4 = k1_xboole_0
% 7.06/1.50      | r1_tarski(sK3,sK7) = iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_53,c_8202]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12278,plain,
% 7.06/1.50      ( r1_tarski(sK3,sK7) = iProver_top ),
% 7.06/1.50      inference(global_propositional_subsumption,
% 7.06/1.50                [status(thm)],
% 7.06/1.50                [c_11812,c_79,c_78,c_81,c_82,c_2312,c_2347]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_12283,plain,
% 7.06/1.50      ( k4_xboole_0(sK3,sK7) = k1_xboole_0 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_12278,c_2161]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_13003,plain,
% 7.06/1.50      ( k4_xboole_0(sK7,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0)
% 7.06/1.50      | k1_xboole_0 = X0 ),
% 7.06/1.50      inference(light_normalisation,[status(thm)],[c_12985,c_12283]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_28,plain,
% 7.06/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.06/1.50      inference(cnf_transformation,[],[f125]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_13004,plain,
% 7.06/1.50      ( sK7 = sK3 | k1_xboole_0 = X0 ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_13003,c_28]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_13561,plain,
% 7.06/1.50      ( sK7 = sK3 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_13004,c_76]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_13753,plain,
% 7.06/1.50      ( k4_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,sK4)) = k2_zfmisc_1(sK3,k4_xboole_0(X0,sK8)) ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_13561,c_8214]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_13764,plain,
% 7.06/1.50      ( k2_zfmisc_1(sK3,k4_xboole_0(X0,sK8)) = k2_zfmisc_1(sK3,k4_xboole_0(X0,sK4)) ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_13753,c_43]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_8209,plain,
% 7.06/1.50      ( k4_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK7,X0)) = k2_zfmisc_1(sK7,k4_xboole_0(sK8,X0)) ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_5825,c_43]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_13755,plain,
% 7.06/1.50      ( k4_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,X0)) = k2_zfmisc_1(sK3,k4_xboole_0(sK8,X0)) ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_13561,c_8209]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_13761,plain,
% 7.06/1.50      ( k2_zfmisc_1(sK3,k4_xboole_0(sK8,X0)) = k2_zfmisc_1(sK3,k4_xboole_0(sK4,X0)) ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_13755,c_43]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_14386,plain,
% 7.06/1.50      ( k2_zfmisc_1(sK3,k4_xboole_0(sK8,sK4)) = k2_zfmisc_1(sK3,k4_xboole_0(sK4,sK8)) ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_13764,c_13761]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_14389,plain,
% 7.06/1.50      ( k2_zfmisc_1(sK3,k4_xboole_0(sK8,sK4)) = k2_zfmisc_1(sK3,k4_xboole_0(sK4,sK4)) ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_14386,c_13764]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_27,plain,
% 7.06/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.06/1.50      inference(cnf_transformation,[],[f195]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2177,plain,
% 7.06/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.06/1.50      inference(light_normalisation,[status(thm)],[c_27,c_28]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_14390,plain,
% 7.06/1.50      ( k2_zfmisc_1(sK3,k4_xboole_0(sK8,sK4)) = k1_xboole_0 ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_14389,c_38,c_2177,c_13761]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_40,plain,
% 7.06/1.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.06/1.50      | k1_xboole_0 = X0
% 7.06/1.50      | k1_xboole_0 = X1 ),
% 7.06/1.50      inference(cnf_transformation,[],[f138]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_14610,plain,
% 7.06/1.50      ( k4_xboole_0(sK8,sK4) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_14390,c_40]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_14722,plain,
% 7.06/1.50      ( k4_xboole_0(sK8,sK4) = k1_xboole_0 ),
% 7.06/1.50      inference(global_propositional_subsumption,
% 7.06/1.50                [status(thm)],
% 7.06/1.50                [c_14610,c_79,c_81,c_82,c_2347]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_14741,plain,
% 7.06/1.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK8)) = k4_xboole_0(sK8,k1_xboole_0) ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_14722,c_3]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_14748,plain,
% 7.06/1.50      ( k4_xboole_0(sK8,k1_xboole_0) = k4_xboole_0(sK4,k1_xboole_0) ),
% 7.06/1.50      inference(light_normalisation,[status(thm)],[c_14741,c_12291]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_14749,plain,
% 7.06/1.50      ( sK8 = sK4 ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_14748,c_28]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_5551,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.50      | sK10 = X2
% 7.06/1.50      | k1_xboole_0 = X0
% 7.06/1.50      | k1_xboole_0 = X1
% 7.06/1.50      | k1_xboole_0 = X2 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_80,c_61]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_64,plain,
% 7.06/1.50      ( X0 = X1
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
% 7.06/1.50      inference(cnf_transformation,[],[f207]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_4900,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10) = k1_xboole_0
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.50      | sK10 = X2 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_80,c_64]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_4908,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k1_xboole_0
% 7.06/1.50      | sK10 = X2 ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_4900,c_80]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_6242,plain,
% 7.06/1.50      ( sK10 = X2
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
% 7.06/1.50      inference(global_propositional_subsumption,
% 7.06/1.50                [status(thm)],
% 7.06/1.50                [c_5551,c_79,c_78,c_77,c_76,c_4908,c_5793]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_6243,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.50      | sK10 = X2 ),
% 7.06/1.50      inference(renaming,[status(thm)],[c_6242]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_6250,plain,
% 7.06/1.50      ( sK10 = sK6 ),
% 7.06/1.50      inference(equality_resolution,[status(thm)],[c_6243]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_75,negated_conjecture,
% 7.06/1.50      ( sK3 != sK7 | sK4 != sK8 | sK5 != sK9 | sK6 != sK10 ),
% 7.06/1.50      inference(cnf_transformation,[],[f182]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_7735,plain,
% 7.06/1.50      ( sK7 != sK3 | sK8 != sK4 | sK9 != sK5 | sK6 != sK6 ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_6250,c_75]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_7738,plain,
% 7.06/1.50      ( sK7 != sK3 | sK8 != sK4 | sK9 != sK5 ),
% 7.06/1.50      inference(equality_resolution_simp,[status(thm)],[c_7735]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_62,plain,
% 7.06/1.50      ( X0 = X1
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
% 7.06/1.50      | k1_xboole_0 = X4
% 7.06/1.50      | k1_xboole_0 = X1
% 7.06/1.50      | k1_xboole_0 = X5 ),
% 7.06/1.50      inference(cnf_transformation,[],[f205]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_5564,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.50      | sK9 = X1
% 7.06/1.50      | k1_xboole_0 = X0
% 7.06/1.50      | k1_xboole_0 = X1
% 7.06/1.50      | k1_xboole_0 = X2 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_80,c_62]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_65,plain,
% 7.06/1.50      ( X0 = X1
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
% 7.06/1.50      inference(cnf_transformation,[],[f208]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_5013,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10) = k1_xboole_0
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.50      | sK9 = X1 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_80,c_65]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_5022,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) = k1_xboole_0
% 7.06/1.50      | sK9 = X1 ),
% 7.06/1.50      inference(demodulation,[status(thm)],[c_5013,c_80]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_6343,plain,
% 7.06/1.50      ( sK9 = X1
% 7.06/1.50      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
% 7.06/1.50      inference(global_propositional_subsumption,
% 7.06/1.50                [status(thm)],
% 7.06/1.50                [c_5564,c_79,c_78,c_77,c_76,c_5022,c_5793]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_6344,plain,
% 7.06/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 7.06/1.50      | sK9 = X1 ),
% 7.06/1.50      inference(renaming,[status(thm)],[c_6343]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_6351,plain,
% 7.06/1.50      ( sK9 = sK5 ),
% 7.06/1.50      inference(equality_resolution,[status(thm)],[c_6344]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_7739,plain,
% 7.06/1.50      ( sK7 != sK3 | sK8 != sK4 | sK5 != sK5 ),
% 7.06/1.50      inference(light_normalisation,[status(thm)],[c_7738,c_6351]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_7740,plain,
% 7.06/1.50      ( sK7 != sK3 | sK8 != sK4 ),
% 7.06/1.50      inference(equality_resolution_simp,[status(thm)],[c_7739]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(contradiction,plain,
% 7.06/1.50      ( $false ),
% 7.06/1.50      inference(minisat,[status(thm)],[c_14749,c_13561,c_7740]) ).
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.06/1.50  
% 7.06/1.50  ------                               Statistics
% 7.06/1.50  
% 7.06/1.50  ------ General
% 7.06/1.50  
% 7.06/1.50  abstr_ref_over_cycles:                  0
% 7.06/1.50  abstr_ref_under_cycles:                 0
% 7.06/1.50  gc_basic_clause_elim:                   0
% 7.06/1.50  forced_gc_time:                         0
% 7.06/1.50  parsing_time:                           0.011
% 7.06/1.50  unif_index_cands_time:                  0.
% 7.06/1.50  unif_index_add_time:                    0.
% 7.06/1.50  orderings_time:                         0.
% 7.06/1.50  out_proof_time:                         0.017
% 7.06/1.50  total_time:                             0.547
% 7.06/1.50  num_of_symbols:                         53
% 7.06/1.50  num_of_terms:                           20260
% 7.06/1.50  
% 7.06/1.50  ------ Preprocessing
% 7.06/1.50  
% 7.06/1.50  num_of_splits:                          0
% 7.06/1.50  num_of_split_atoms:                     0
% 7.06/1.50  num_of_reused_defs:                     0
% 7.06/1.50  num_eq_ax_congr_red:                    33
% 7.06/1.50  num_of_sem_filtered_clauses:            1
% 7.06/1.50  num_of_subtypes:                        0
% 7.06/1.50  monotx_restored_types:                  0
% 7.06/1.50  sat_num_of_epr_types:                   0
% 7.06/1.50  sat_num_of_non_cyclic_types:            0
% 7.06/1.50  sat_guarded_non_collapsed_types:        0
% 7.06/1.50  num_pure_diseq_elim:                    0
% 7.06/1.50  simp_replaced_by:                       0
% 7.06/1.50  res_preprocessed:                       343
% 7.06/1.50  prep_upred:                             0
% 7.06/1.50  prep_unflattend:                        0
% 7.06/1.50  smt_new_axioms:                         0
% 7.06/1.50  pred_elim_cands:                        4
% 7.06/1.50  pred_elim:                              0
% 7.06/1.50  pred_elim_cl:                           0
% 7.06/1.50  pred_elim_cycles:                       2
% 7.06/1.50  merged_defs:                            40
% 7.06/1.50  merged_defs_ncl:                        0
% 7.06/1.50  bin_hyper_res:                          40
% 7.06/1.50  prep_cycles:                            4
% 7.06/1.50  pred_elim_time:                         0.002
% 7.06/1.50  splitting_time:                         0.
% 7.06/1.50  sem_filter_time:                        0.
% 7.06/1.50  monotx_time:                            0.001
% 7.06/1.50  subtype_inf_time:                       0.
% 7.06/1.50  
% 7.06/1.50  ------ Problem properties
% 7.06/1.50  
% 7.06/1.50  clauses:                                80
% 7.06/1.50  conjectures:                            6
% 7.06/1.50  epr:                                    14
% 7.06/1.50  horn:                                   58
% 7.06/1.50  ground:                                 9
% 7.06/1.50  unary:                                  29
% 7.06/1.50  binary:                                 30
% 7.06/1.50  lits:                                   162
% 7.06/1.50  lits_eq:                                87
% 7.06/1.50  fd_pure:                                0
% 7.06/1.50  fd_pseudo:                              0
% 7.06/1.50  fd_cond:                                7
% 7.06/1.50  fd_pseudo_cond:                         7
% 7.06/1.50  ac_symbols:                             0
% 7.06/1.50  
% 7.06/1.50  ------ Propositional Solver
% 7.06/1.50  
% 7.06/1.50  prop_solver_calls:                      29
% 7.06/1.50  prop_fast_solver_calls:                 2021
% 7.06/1.50  smt_solver_calls:                       0
% 7.06/1.50  smt_fast_solver_calls:                  0
% 7.06/1.50  prop_num_of_clauses:                    7789
% 7.06/1.50  prop_preprocess_simplified:             19026
% 7.06/1.50  prop_fo_subsumed:                       55
% 7.06/1.50  prop_solver_time:                       0.
% 7.06/1.50  smt_solver_time:                        0.
% 7.06/1.50  smt_fast_solver_time:                   0.
% 7.06/1.50  prop_fast_solver_time:                  0.
% 7.06/1.50  prop_unsat_core_time:                   0.
% 7.06/1.50  
% 7.06/1.50  ------ QBF
% 7.06/1.50  
% 7.06/1.50  qbf_q_res:                              0
% 7.06/1.50  qbf_num_tautologies:                    0
% 7.06/1.50  qbf_prep_cycles:                        0
% 7.06/1.50  
% 7.06/1.50  ------ BMC1
% 7.06/1.50  
% 7.06/1.50  bmc1_current_bound:                     -1
% 7.06/1.50  bmc1_last_solved_bound:                 -1
% 7.06/1.50  bmc1_unsat_core_size:                   -1
% 7.06/1.50  bmc1_unsat_core_parents_size:           -1
% 7.06/1.50  bmc1_merge_next_fun:                    0
% 7.06/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.06/1.50  
% 7.06/1.50  ------ Instantiation
% 7.06/1.50  
% 7.06/1.50  inst_num_of_clauses:                    3217
% 7.06/1.50  inst_num_in_passive:                    888
% 7.06/1.50  inst_num_in_active:                     854
% 7.06/1.50  inst_num_in_unprocessed:                1475
% 7.06/1.50  inst_num_of_loops:                      870
% 7.06/1.50  inst_num_of_learning_restarts:          0
% 7.06/1.50  inst_num_moves_active_passive:          16
% 7.06/1.50  inst_lit_activity:                      0
% 7.06/1.50  inst_lit_activity_moves:                0
% 7.06/1.50  inst_num_tautologies:                   0
% 7.06/1.50  inst_num_prop_implied:                  0
% 7.06/1.50  inst_num_existing_simplified:           0
% 7.06/1.50  inst_num_eq_res_simplified:             0
% 7.06/1.50  inst_num_child_elim:                    0
% 7.06/1.50  inst_num_of_dismatching_blockings:      31
% 7.06/1.50  inst_num_of_non_proper_insts:           3334
% 7.06/1.50  inst_num_of_duplicates:                 0
% 7.06/1.50  inst_inst_num_from_inst_to_res:         0
% 7.06/1.50  inst_dismatching_checking_time:         0.
% 7.06/1.50  
% 7.06/1.50  ------ Resolution
% 7.06/1.50  
% 7.06/1.50  res_num_of_clauses:                     0
% 7.06/1.50  res_num_in_passive:                     0
% 7.06/1.50  res_num_in_active:                      0
% 7.06/1.50  res_num_of_loops:                       347
% 7.06/1.50  res_forward_subset_subsumed:            66
% 7.06/1.50  res_backward_subset_subsumed:           0
% 7.06/1.50  res_forward_subsumed:                   0
% 7.06/1.50  res_backward_subsumed:                  0
% 7.06/1.50  res_forward_subsumption_resolution:     0
% 7.06/1.50  res_backward_subsumption_resolution:    0
% 7.06/1.50  res_clause_to_clause_subsumption:       4308
% 7.06/1.50  res_orphan_elimination:                 0
% 7.06/1.50  res_tautology_del:                      81
% 7.06/1.50  res_num_eq_res_simplified:              0
% 7.06/1.50  res_num_sel_changes:                    0
% 7.06/1.50  res_moves_from_active_to_pass:          0
% 7.06/1.50  
% 7.06/1.50  ------ Superposition
% 7.06/1.50  
% 7.06/1.50  sup_time_total:                         0.
% 7.06/1.50  sup_time_generating:                    0.
% 7.06/1.50  sup_time_sim_full:                      0.
% 7.06/1.50  sup_time_sim_immed:                     0.
% 7.06/1.50  
% 7.06/1.50  sup_num_of_clauses:                     791
% 7.06/1.50  sup_num_in_active:                      108
% 7.06/1.50  sup_num_in_passive:                     683
% 7.06/1.50  sup_num_of_loops:                       173
% 7.06/1.50  sup_fw_superposition:                   712
% 7.06/1.50  sup_bw_superposition:                   2033
% 7.06/1.50  sup_immediate_simplified:               1757
% 7.06/1.50  sup_given_eliminated:                   4
% 7.06/1.50  comparisons_done:                       0
% 7.06/1.50  comparisons_avoided:                    9
% 7.06/1.50  
% 7.06/1.50  ------ Simplifications
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  sim_fw_subset_subsumed:                 898
% 7.06/1.50  sim_bw_subset_subsumed:                 41
% 7.06/1.50  sim_fw_subsumed:                        257
% 7.06/1.50  sim_bw_subsumed:                        50
% 7.06/1.50  sim_fw_subsumption_res:                 0
% 7.06/1.50  sim_bw_subsumption_res:                 0
% 7.06/1.50  sim_tautology_del:                      53
% 7.06/1.50  sim_eq_tautology_del:                   184
% 7.06/1.50  sim_eq_res_simp:                        3
% 7.06/1.50  sim_fw_demodulated:                     530
% 7.06/1.50  sim_bw_demodulated:                     62
% 7.06/1.50  sim_light_normalised:                   353
% 7.06/1.50  sim_joinable_taut:                      0
% 7.06/1.50  sim_joinable_simp:                      0
% 7.06/1.50  sim_ac_normalised:                      0
% 7.06/1.50  sim_smt_subsumption:                    0
% 7.06/1.50  
%------------------------------------------------------------------------------
