%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:40 EST 2020

% Result     : Theorem 28.83s
% Output     : Refutation 28.83s
% Verified   : 
% Statistics : Number of formulae       :  193 (1328 expanded)
%              Number of leaves         :   36 ( 385 expanded)
%              Depth                    :   32
%              Number of atoms          :  717 (3705 expanded)
%              Number of equality atoms :  288 (1658 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28877,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f177,f27666,f2721])).

fof(f2721,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k9_relat_1(sK3,X3),k1_zfmisc_1(X2))
      | ~ r1_tarski(k2_relat_1(sK3),X2) ) ),
    inference(subsumption_resolution,[],[f2711,f221])).

fof(f221,plain,(
    ! [X2] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2)))
      | ~ r1_tarski(k2_relat_1(sK3),X2) ) ),
    inference(resolution,[],[f155,f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f155,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f86,f153])).

fof(f153,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f91,f152])).

fof(f152,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f103,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f120,f150])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f127,f149])).

fof(f149,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f133,f148])).

fof(f148,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f134,f147])).

fof(f147,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f134,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f133,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f127,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f120,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f103,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f91,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f61])).

fof(f61,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f2711,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k9_relat_1(sK3,X3),k1_zfmisc_1(X2))
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2))) ) ),
    inference(superposition,[],[f650,f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f650,plain,(
    ! [X6,X5] :
      ( m1_subset_1(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X5,sK3,X6),k1_zfmisc_1(X5))
      | ~ r1_tarski(k2_relat_1(sK3),X5) ) ),
    inference(resolution,[],[f221,f128])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f27666,plain,(
    ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f27665,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f27665,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f27625,f14120])).

fof(f14120,plain,(
    r2_hidden(sK0,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f10636,f13974])).

fof(f13974,plain,(
    sK0 = sK7(k1_relat_1(sK3),k1_xboole_0) ),
    inference(resolution,[],[f12944,f10636])).

fof(f12944,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | sK0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f12916])).

fof(f12916,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0 ) ),
    inference(resolution,[],[f1487,f190])).

fof(f190,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( X4 = X7
      | X3 = X7
      | X2 = X7
      | X1 = X7
      | X0 = X7
      | ~ r2_hidden(X7,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ) ),
    inference(equality_resolution,[],[f170])).

fof(f170,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X4 = X7
      | X3 = X7
      | X2 = X7
      | X1 = X7
      | X0 = X7
      | ~ r2_hidden(X7,X5)
      | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f135,f149])).

fof(f135,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X4 = X7
      | X3 = X7
      | X2 = X7
      | X1 = X7
      | X0 = X7
      | ~ r2_hidden(X7,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ( ( ( sK8(X0,X1,X2,X3,X4,X5) != X4
              & sK8(X0,X1,X2,X3,X4,X5) != X3
              & sK8(X0,X1,X2,X3,X4,X5) != X2
              & sK8(X0,X1,X2,X3,X4,X5) != X1
              & sK8(X0,X1,X2,X3,X4,X5) != X0 )
            | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK8(X0,X1,X2,X3,X4,X5) = X4
            | sK8(X0,X1,X2,X3,X4,X5) = X3
            | sK8(X0,X1,X2,X3,X4,X5) = X2
            | sK8(X0,X1,X2,X3,X4,X5) = X1
            | sK8(X0,X1,X2,X3,X4,X5) = X0
            | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f81,f82])).

fof(f82,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK8(X0,X1,X2,X3,X4,X5) != X4
            & sK8(X0,X1,X2,X3,X4,X5) != X3
            & sK8(X0,X1,X2,X3,X4,X5) != X2
            & sK8(X0,X1,X2,X3,X4,X5) != X1
            & sK8(X0,X1,X2,X3,X4,X5) != X0 )
          | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK8(X0,X1,X2,X3,X4,X5) = X4
          | sK8(X0,X1,X2,X3,X4,X5) = X3
          | sK8(X0,X1,X2,X3,X4,X5) = X2
          | sK8(X0,X1,X2,X3,X4,X5) = X1
          | sK8(X0,X1,X2,X3,X4,X5) = X0
          | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(rectify,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(f1487,plain,(
    ! [X2] :
      ( r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X2,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f341,f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f73,f74])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f341,plain,(
    r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f333,f236])).

fof(f236,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f227,f102])).

fof(f102,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f227,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(resolution,[],[f155,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f333,plain,
    ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f215,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f215,plain,(
    v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f155,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f10636,plain,(
    r2_hidden(sK7(k1_relat_1(sK3),k1_xboole_0),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f1282,f10538])).

fof(f10538,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f10537])).

fof(f10537,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f10536,f179])).

fof(f179,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f10536,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(subsumption_resolution,[],[f10529,f10380])).

fof(f10380,plain,(
    ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(resolution,[],[f9994,f1019])).

fof(f1019,plain,(
    r2_hidden(sK6(sK3,sK2,sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f1018,f236])).

fof(f1018,plain,
    ( r2_hidden(sK6(sK3,sK2,sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f997,f84])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f997,plain,
    ( r2_hidden(sK6(sK3,sK2,sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f600,f175])).

fof(f175,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
                  & r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
                    & r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f64,f67,f66,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
        & r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f600,plain,(
    r2_hidden(sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k9_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f566,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f566,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f154,f220])).

fof(f220,plain,(
    ! [X1] : k9_relat_1(sK3,X1) = k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X1) ),
    inference(resolution,[],[f155,f129])).

fof(f154,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f88,f153,f153])).

fof(f88,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f9994,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f9964,f111])).

fof(f9964,plain,(
    ! [X8] : ~ r2_hidden(X8,k1_xboole_0) ),
    inference(resolution,[],[f2268,f89])).

fof(f89,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2268,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f2218,f111])).

fof(f2218,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f2179,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f2179,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f2178,f90])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f2178,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f1364,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1364,plain,(
    ! [X0,X1] : r1_tarski(k1_relset_1(X0,X1,k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f1363,f90])).

fof(f1363,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relset_1(X0,X1,k1_xboole_0),X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f316,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f316,plain,(
    ! [X12,X10,X11] : r1_tarski(k8_relset_1(X10,X11,k1_xboole_0,X12),X10) ),
    inference(subsumption_resolution,[],[f308,f90])).

fof(f308,plain,(
    ! [X12,X10,X11] :
      ( r1_tarski(k8_relset_1(X10,X11,k1_xboole_0,X12),X10)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(resolution,[],[f299,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

fof(f299,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f297,f90])).

fof(f297,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
      | v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f191,f236])).

fof(f191,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f84,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f10529,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f1540,f121])).

fof(f1540,plain,(
    ! [X1] :
      ( r1_tarski(k1_relset_1(k1_xboole_0,X1,sK3),k1_xboole_0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f353,f179])).

fof(f353,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k1_relset_1(X0,X1,sK3),X0) ) ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relset_1(X0,X1,sK3),X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f196,f125])).

fof(f196,plain,(
    ! [X12,X10,X11] :
      ( r1_tarski(k8_relset_1(X10,X11,sK3,X12),X10)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(resolution,[],[f84,f132])).

fof(f1282,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(sK7(k1_relat_1(sK3),k1_xboole_0),k1_relat_1(sK3)) ),
    inference(resolution,[],[f331,f112])).

fof(f331,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f222,f179])).

fof(f222,plain,(
    ! [X3] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
      | ~ r1_tarski(k1_relat_1(sK3),X3) ) ),
    inference(resolution,[],[f155,f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f27625,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3)))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f27538])).

fof(f27538,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3)))
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(superposition,[],[f2566,f27482])).

fof(f27482,plain,
    ( sK0 = sK8(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f4572,f12944])).

fof(f4572,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK3))
    | r2_hidden(sK8(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK3)),k1_relat_1(sK3)) ),
    inference(equality_resolution,[],[f729])).

fof(f729,plain,(
    ! [X0] :
      ( k1_relat_1(sK3) != X0
      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
      | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0)
      | r2_hidden(sK8(sK0,sK0,sK0,sK0,sK0,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f723])).

fof(f723,plain,(
    ! [X0] :
      ( k1_relat_1(sK3) != X0
      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
      | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0)
      | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0)
      | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0)
      | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0)
      | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0)
      | r2_hidden(sK8(sK0,sK0,sK0,sK0,sK0,X0),X0) ) ),
    inference(superposition,[],[f623,f164])).

fof(f164,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = X5
      | sK8(X0,X1,X2,X3,X4,X5) = X4
      | sK8(X0,X1,X2,X3,X4,X5) = X3
      | sK8(X0,X1,X2,X3,X4,X5) = X2
      | sK8(X0,X1,X2,X3,X4,X5) = X1
      | sK8(X0,X1,X2,X3,X4,X5) = X0
      | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ),
    inference(definition_unfolding,[],[f141,f149])).

fof(f141,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
      | sK8(X0,X1,X2,X3,X4,X5) = X4
      | sK8(X0,X1,X2,X3,X4,X5) = X3
      | sK8(X0,X1,X2,X3,X4,X5) = X2
      | sK8(X0,X1,X2,X3,X4,X5) = X1
      | sK8(X0,X1,X2,X3,X4,X5) = X0
      | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f623,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f622,f236])).

fof(f622,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f606,f84])).

fof(f606,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f566,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f107,f153,f153])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f2566,plain,(
    ! [X1] :
      ( sK0 != sK8(sK0,sK0,sK0,sK0,sK0,X1)
      | ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3)))
      | k1_relat_1(sK3) != X1
      | ~ r2_hidden(sK0,X1) ) ),
    inference(inner_rewriting,[],[f2560])).

fof(f2560,plain,(
    ! [X1] :
      ( k1_relat_1(sK3) != X1
      | ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3)))
      | sK0 != sK8(sK0,sK0,sK0,sK0,sK0,X1)
      | ~ r2_hidden(sK8(sK0,sK0,sK0,sK0,sK0,X1),X1) ) ),
    inference(superposition,[],[f967,f163])).

fof(f163,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = X5
      | sK8(X0,X1,X2,X3,X4,X5) != X0
      | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ),
    inference(definition_unfolding,[],[f142,f149])).

fof(f142,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
      | sK8(X0,X1,X2,X3,X4,X5) != X0
      | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f967,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f966,f236])).

fof(f966,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3)))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f950,f84])).

fof(f950,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3)))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f599,f158])).

fof(f599,plain,(
    ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))) ),
    inference(resolution,[],[f566,f114])).

fof(f177,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:35:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (820510720)
% 0.13/0.37  ipcrm: permission denied for id (820543489)
% 0.13/0.37  ipcrm: permission denied for id (820576260)
% 0.13/0.38  ipcrm: permission denied for id (820641803)
% 0.13/0.39  ipcrm: permission denied for id (820674579)
% 0.13/0.39  ipcrm: permission denied for id (820707350)
% 0.13/0.40  ipcrm: permission denied for id (820740125)
% 0.21/0.41  ipcrm: permission denied for id (820772899)
% 0.21/0.44  ipcrm: permission denied for id (820871225)
% 0.21/0.44  ipcrm: permission denied for id (820903994)
% 0.21/0.45  ipcrm: permission denied for id (820936769)
% 0.21/0.48  ipcrm: permission denied for id (821002328)
% 0.21/0.51  ipcrm: permission denied for id (821100654)
% 0.21/0.52  ipcrm: permission denied for id (821166198)
% 1.11/0.68  % (8499)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.11/0.68  % (8507)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.11/0.71  % (8492)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.72  % (8496)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.72  % (8495)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.72  % (8500)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.46/0.72  % (8512)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.72  % (8493)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.73  % (8508)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.74  % (8504)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.74  % (8502)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.74  % (8509)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.71/0.74  % (8501)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.71/0.76  % (8494)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.71/0.76  % (8510)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.71/0.76  % (8487)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.71/0.76  % (8488)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.71/0.76  % (8506)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.71/0.77  % (8489)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.71/0.77  % (8486)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.71/0.77  % (8498)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.71/0.77  % (8514)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.71/0.78  % (8511)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.71/0.78  % (8491)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.71/0.78  % (8485)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.71/0.78  % (8503)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.71/0.78  % (8487)Refutation not found, incomplete strategy% (8487)------------------------------
% 1.71/0.78  % (8487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.78  % (8487)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.78  
% 1.71/0.78  % (8487)Memory used [KB]: 10874
% 1.71/0.78  % (8487)Time elapsed: 0.187 s
% 1.71/0.78  % (8487)------------------------------
% 1.71/0.78  % (8487)------------------------------
% 1.71/0.78  % (8505)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.71/0.78  % (8513)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.71/0.79  % (8490)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.71/0.79  % (8497)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 3.32/0.95  % (8543)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.41/0.98  % (8490)Time limit reached!
% 3.41/0.98  % (8490)------------------------------
% 3.41/0.98  % (8490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.41/0.99  % (8490)Termination reason: Time limit
% 3.41/0.99  % (8490)Termination phase: Saturation
% 3.41/0.99  
% 3.41/0.99  % (8490)Memory used [KB]: 7803
% 3.41/0.99  % (8490)Time elapsed: 0.400 s
% 3.41/0.99  % (8490)------------------------------
% 3.41/0.99  % (8490)------------------------------
% 4.03/1.10  % (8653)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.03/1.10  % (8486)Time limit reached!
% 4.03/1.10  % (8486)------------------------------
% 4.03/1.10  % (8486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/1.10  % (8486)Termination reason: Time limit
% 4.03/1.10  
% 4.03/1.10  % (8486)Memory used [KB]: 7931
% 4.03/1.10  % (8486)Time elapsed: 0.511 s
% 4.03/1.10  % (8486)------------------------------
% 4.03/1.10  % (8486)------------------------------
% 4.03/1.11  % (8495)Time limit reached!
% 4.03/1.11  % (8495)------------------------------
% 4.03/1.11  % (8495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/1.11  % (8495)Termination reason: Time limit
% 4.03/1.11  
% 4.03/1.11  % (8495)Memory used [KB]: 19189
% 4.03/1.11  % (8495)Time elapsed: 0.513 s
% 4.03/1.11  % (8495)------------------------------
% 4.03/1.11  % (8495)------------------------------
% 4.03/1.11  % (8497)Time limit reached!
% 4.03/1.11  % (8497)------------------------------
% 4.03/1.11  % (8497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/1.11  % (8497)Termination reason: Time limit
% 4.03/1.11  
% 4.03/1.11  % (8497)Memory used [KB]: 8315
% 4.03/1.11  % (8497)Time elapsed: 0.511 s
% 4.03/1.11  % (8497)------------------------------
% 4.03/1.11  % (8497)------------------------------
% 4.03/1.13  % (8485)Time limit reached!
% 4.03/1.13  % (8485)------------------------------
% 4.03/1.13  % (8485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/1.13  % (8485)Termination reason: Time limit
% 4.03/1.13  
% 4.03/1.13  % (8485)Memory used [KB]: 3198
% 4.03/1.13  % (8485)Time elapsed: 0.511 s
% 4.03/1.13  % (8485)------------------------------
% 4.03/1.13  % (8485)------------------------------
% 4.84/1.16  % (8502)Time limit reached!
% 4.84/1.16  % (8502)------------------------------
% 4.84/1.16  % (8502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.18  % (8502)Termination reason: Time limit
% 4.84/1.18  % (8502)Termination phase: Saturation
% 4.84/1.18  
% 4.84/1.18  % (8502)Memory used [KB]: 16375
% 4.84/1.18  % (8502)Time elapsed: 0.500 s
% 4.84/1.18  % (8502)------------------------------
% 4.84/1.18  % (8502)------------------------------
% 5.22/1.20  % (8492)Time limit reached!
% 5.22/1.20  % (8492)------------------------------
% 5.22/1.20  % (8492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.22/1.20  % (8492)Termination reason: Time limit
% 5.22/1.20  % (8492)Termination phase: Saturation
% 5.22/1.20  
% 5.22/1.20  % (8492)Memory used [KB]: 10874
% 5.22/1.20  % (8492)Time elapsed: 0.600 s
% 5.22/1.20  % (8492)------------------------------
% 5.22/1.20  % (8492)------------------------------
% 5.22/1.21  % (8501)Time limit reached!
% 5.22/1.21  % (8501)------------------------------
% 5.22/1.21  % (8501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.22/1.21  % (8501)Termination reason: Time limit
% 5.22/1.21  
% 5.22/1.21  % (8501)Memory used [KB]: 15351
% 5.22/1.21  % (8501)Time elapsed: 0.613 s
% 5.22/1.21  % (8501)------------------------------
% 5.22/1.21  % (8501)------------------------------
% 5.22/1.23  % (8681)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.22/1.23  % (8685)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.22/1.25  % (8686)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.78/1.27  % (8690)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.05/1.33  % (8709)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.05/1.33  % (8703)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.05/1.33  % (8713)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.27/1.36  % (8513)Time limit reached!
% 6.27/1.36  % (8513)------------------------------
% 6.27/1.36  % (8513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.27/1.38  % (8513)Termination reason: Time limit
% 6.27/1.38  % (8513)Termination phase: Saturation
% 6.27/1.38  
% 6.27/1.38  % (8513)Memory used [KB]: 7675
% 6.27/1.38  % (8513)Time elapsed: 0.600 s
% 6.27/1.38  % (8513)------------------------------
% 6.27/1.38  % (8513)------------------------------
% 6.27/1.41  % (8506)Time limit reached!
% 6.27/1.41  % (8506)------------------------------
% 6.27/1.41  % (8506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.27/1.41  % (8506)Termination reason: Time limit
% 6.27/1.41  % (8506)Termination phase: Saturation
% 6.27/1.41  
% 6.27/1.41  % (8506)Memory used [KB]: 4093
% 6.27/1.41  % (8506)Time elapsed: 0.800 s
% 6.27/1.41  % (8506)------------------------------
% 6.27/1.41  % (8506)------------------------------
% 7.40/1.50  % (8754)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.40/1.54  % (8685)Time limit reached!
% 7.40/1.54  % (8685)------------------------------
% 7.40/1.54  % (8685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.40/1.54  % (8685)Termination reason: Time limit
% 7.40/1.54  % (8685)Termination phase: Saturation
% 7.40/1.54  
% 7.40/1.54  % (8685)Memory used [KB]: 7931
% 7.40/1.54  % (8685)Time elapsed: 0.400 s
% 7.40/1.54  % (8685)------------------------------
% 7.40/1.54  % (8685)------------------------------
% 7.40/1.55  % (8686)Time limit reached!
% 7.40/1.55  % (8686)------------------------------
% 7.40/1.55  % (8686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.40/1.55  % (8686)Termination reason: Time limit
% 7.40/1.55  
% 7.40/1.55  % (8686)Memory used [KB]: 13304
% 7.40/1.55  % (8686)Time elapsed: 0.408 s
% 7.40/1.55  % (8686)------------------------------
% 7.40/1.55  % (8686)------------------------------
% 7.40/1.55  % (8755)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.82/1.67  % (8756)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.82/1.67  % (8757)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 10.06/1.83  % (8507)Time limit reached!
% 10.06/1.83  % (8507)------------------------------
% 10.06/1.83  % (8507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.06/1.83  % (8507)Termination reason: Time limit
% 10.06/1.83  
% 10.06/1.83  % (8507)Memory used [KB]: 16630
% 10.06/1.83  % (8507)Time elapsed: 1.206 s
% 10.06/1.83  % (8507)------------------------------
% 10.06/1.83  % (8507)------------------------------
% 10.56/1.86  % (8511)Time limit reached!
% 10.56/1.86  % (8511)------------------------------
% 10.56/1.86  % (8511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.56/1.87  % (8511)Termination reason: Time limit
% 10.56/1.87  
% 10.56/1.87  % (8511)Memory used [KB]: 26481
% 10.56/1.87  % (8511)Time elapsed: 1.262 s
% 10.56/1.87  % (8511)------------------------------
% 10.56/1.87  % (8511)------------------------------
% 10.56/1.90  % (8500)Time limit reached!
% 10.56/1.90  % (8500)------------------------------
% 10.56/1.90  % (8500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.56/1.90  % (8500)Termination reason: Time limit
% 10.56/1.90  
% 10.56/1.90  % (8500)Memory used [KB]: 14456
% 10.56/1.90  % (8500)Time elapsed: 1.305 s
% 10.56/1.90  % (8500)------------------------------
% 10.56/1.90  % (8500)------------------------------
% 10.56/1.95  % (8758)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 11.28/1.98  % (8759)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.55/2.02  % (8760)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.83/2.07  % (8757)Time limit reached!
% 11.83/2.07  % (8757)------------------------------
% 11.83/2.07  % (8757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.83/2.09  % (8757)Termination reason: Time limit
% 11.83/2.09  % (8757)Termination phase: Saturation
% 11.83/2.09  
% 11.83/2.09  % (8757)Memory used [KB]: 2558
% 11.83/2.09  % (8757)Time elapsed: 0.500 s
% 11.83/2.09  % (8757)------------------------------
% 11.83/2.09  % (8757)------------------------------
% 12.32/2.13  % (8512)Time limit reached!
% 12.32/2.13  % (8512)------------------------------
% 12.32/2.13  % (8512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.32/2.14  % (8512)Termination reason: Time limit
% 12.32/2.14  
% 12.32/2.14  % (8512)Memory used [KB]: 13432
% 12.32/2.14  % (8512)Time elapsed: 1.536 s
% 12.32/2.14  % (8512)------------------------------
% 12.32/2.14  % (8512)------------------------------
% 12.72/2.18  % (8761)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 13.34/2.26  % (8509)Time limit reached!
% 13.34/2.26  % (8509)------------------------------
% 13.34/2.26  % (8509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.34/2.26  % (8509)Termination reason: Time limit
% 13.34/2.26  
% 13.34/2.26  % (8509)Memory used [KB]: 32366
% 13.34/2.26  % (8509)Time elapsed: 1.646 s
% 13.34/2.26  % (8509)------------------------------
% 13.34/2.26  % (8509)------------------------------
% 13.34/2.27  % (8496)Time limit reached!
% 13.34/2.27  % (8496)------------------------------
% 13.34/2.27  % (8496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.34/2.27  % (8496)Termination reason: Time limit
% 13.34/2.27  
% 13.34/2.27  % (8496)Memory used [KB]: 30063
% 13.34/2.27  % (8496)Time elapsed: 1.626 s
% 13.34/2.27  % (8496)------------------------------
% 13.34/2.27  % (8496)------------------------------
% 13.34/2.28  % (8762)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 14.05/2.30  % (8489)Time limit reached!
% 14.05/2.30  % (8489)------------------------------
% 14.05/2.30  % (8489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.05/2.31  % (8489)Termination reason: Time limit
% 14.05/2.31  % (8489)Termination phase: Saturation
% 14.05/2.31  
% 14.05/2.31  % (8489)Memory used [KB]: 28016
% 14.05/2.31  % (8489)Time elapsed: 1.708 s
% 14.05/2.31  % (8489)------------------------------
% 14.05/2.31  % (8489)------------------------------
% 14.83/2.43  % (8763)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 14.83/2.44  % (8764)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 15.19/2.46  % (8765)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 15.19/2.50  % (8761)Time limit reached!
% 15.19/2.50  % (8761)------------------------------
% 15.19/2.50  % (8761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.19/2.51  % (8761)Termination reason: Time limit
% 15.19/2.51  % (8761)Termination phase: Saturation
% 15.19/2.51  
% 15.19/2.51  % (8761)Memory used [KB]: 4221
% 15.19/2.51  % (8761)Time elapsed: 0.400 s
% 15.19/2.51  % (8761)------------------------------
% 15.19/2.51  % (8761)------------------------------
% 16.24/2.62  % (8766)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 16.24/2.63  % (8491)Time limit reached!
% 16.24/2.63  % (8491)------------------------------
% 16.24/2.63  % (8491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.24/2.63  % (8491)Termination reason: Time limit
% 16.24/2.63  % (8491)Termination phase: Saturation
% 16.24/2.63  
% 16.24/2.63  % (8491)Memory used [KB]: 22899
% 16.24/2.63  % (8491)Time elapsed: 2.032 s
% 16.24/2.63  % (8491)------------------------------
% 16.24/2.63  % (8491)------------------------------
% 16.24/2.63  % (8499)Time limit reached!
% 16.24/2.63  % (8499)------------------------------
% 16.24/2.63  % (8499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.24/2.63  % (8499)Termination reason: Time limit
% 16.24/2.63  % (8499)Termination phase: Saturation
% 16.24/2.63  
% 16.24/2.63  % (8499)Memory used [KB]: 13432
% 16.24/2.63  % (8499)Time elapsed: 1.800 s
% 16.24/2.63  % (8499)------------------------------
% 16.24/2.63  % (8499)------------------------------
% 16.64/2.65  % (8703)Time limit reached!
% 16.64/2.65  % (8703)------------------------------
% 16.64/2.65  % (8703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.64/2.65  % (8703)Termination reason: Time limit
% 16.64/2.65  
% 16.64/2.65  % (8703)Memory used [KB]: 26097
% 16.64/2.65  % (8703)Time elapsed: 1.423 s
% 16.64/2.65  % (8703)------------------------------
% 16.64/2.65  % (8703)------------------------------
% 16.99/2.73  % (8764)Time limit reached!
% 16.99/2.73  % (8764)------------------------------
% 16.99/2.73  % (8764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.99/2.74  % (8764)Termination reason: Time limit
% 16.99/2.74  
% 16.99/2.74  % (8764)Memory used [KB]: 2686
% 16.99/2.74  % (8764)Time elapsed: 0.412 s
% 16.99/2.74  % (8764)------------------------------
% 16.99/2.74  % (8764)------------------------------
% 17.44/2.76  % (8767)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 17.44/2.77  % (8768)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 17.44/2.78  % (8769)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.44/2.85  % (8503)Time limit reached!
% 17.44/2.85  % (8503)------------------------------
% 17.44/2.85  % (8503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.44/2.85  % (8503)Termination reason: Time limit
% 17.44/2.85  % (8503)Termination phase: Saturation
% 17.44/2.85  
% 17.44/2.85  % (8503)Memory used [KB]: 16886
% 17.44/2.85  % (8503)Time elapsed: 2.0000 s
% 17.44/2.85  % (8503)------------------------------
% 17.44/2.85  % (8503)------------------------------
% 17.44/2.85  % (8681)Time limit reached!
% 17.44/2.85  % (8681)------------------------------
% 17.44/2.85  % (8681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.46/2.87  % (8681)Termination reason: Time limit
% 18.46/2.87  
% 18.46/2.87  % (8681)Memory used [KB]: 18038
% 18.46/2.87  % (8681)Time elapsed: 1.723 s
% 18.46/2.87  % (8681)------------------------------
% 18.46/2.87  % (8681)------------------------------
% 18.46/2.89  % (8770)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 18.46/2.89  % (8770)Refutation not found, incomplete strategy% (8770)------------------------------
% 18.46/2.89  % (8770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.46/2.89  % (8770)Termination reason: Refutation not found, incomplete strategy
% 18.46/2.89  
% 18.46/2.89  % (8770)Memory used [KB]: 6396
% 18.46/2.89  % (8770)Time elapsed: 0.084 s
% 18.46/2.89  % (8770)------------------------------
% 18.46/2.89  % (8770)------------------------------
% 19.24/3.00  % (8771)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 19.24/3.01  % (8772)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 20.26/3.13  % (8493)Time limit reached!
% 20.26/3.13  % (8493)------------------------------
% 20.26/3.13  % (8493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.26/3.13  % (8493)Termination reason: Time limit
% 20.26/3.13  % (8493)Termination phase: Saturation
% 20.26/3.13  
% 20.26/3.13  % (8493)Memory used [KB]: 17526
% 20.26/3.13  % (8493)Time elapsed: 2.500 s
% 20.26/3.13  % (8493)------------------------------
% 20.26/3.13  % (8493)------------------------------
% 20.26/3.13  % (8760)Time limit reached!
% 20.26/3.13  % (8760)------------------------------
% 20.26/3.13  % (8760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.26/3.13  % (8760)Termination reason: Time limit
% 20.26/3.13  % (8760)Termination phase: Saturation
% 20.26/3.13  
% 20.26/3.13  % (8760)Memory used [KB]: 15735
% 20.26/3.13  % (8760)Time elapsed: 1.200 s
% 20.26/3.13  % (8760)------------------------------
% 20.26/3.13  % (8760)------------------------------
% 21.07/3.22  % (8769)Time limit reached!
% 21.07/3.22  % (8769)------------------------------
% 21.07/3.22  % (8769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.07/3.22  % (8769)Termination reason: Time limit
% 21.07/3.22  % (8769)Termination phase: Saturation
% 21.07/3.22  
% 21.07/3.22  % (8769)Memory used [KB]: 10746
% 21.07/3.22  % (8769)Time elapsed: 0.400 s
% 21.07/3.22  % (8769)------------------------------
% 21.07/3.22  % (8769)------------------------------
% 21.44/3.28  % (8504)Time limit reached!
% 21.44/3.28  % (8504)------------------------------
% 21.44/3.28  % (8504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.44/3.29  % (8504)Termination reason: Time limit
% 21.44/3.29  
% 21.44/3.29  % (8504)Memory used [KB]: 21108
% 21.44/3.29  % (8504)Time elapsed: 2.666 s
% 21.44/3.29  % (8504)------------------------------
% 21.44/3.29  % (8504)------------------------------
% 21.44/3.30  % (8771)Time limit reached!
% 21.44/3.30  % (8771)------------------------------
% 21.44/3.30  % (8771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.44/3.30  % (8771)Termination reason: Time limit
% 21.44/3.30  % (8771)Termination phase: Saturation
% 21.44/3.30  
% 21.44/3.30  % (8771)Memory used [KB]: 12792
% 21.44/3.30  % (8771)Time elapsed: 0.400 s
% 21.44/3.30  % (8771)------------------------------
% 21.44/3.30  % (8771)------------------------------
% 24.07/3.64  % (8713)Time limit reached!
% 24.07/3.64  % (8713)------------------------------
% 24.07/3.64  % (8713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.76/3.65  % (8713)Termination reason: Time limit
% 24.76/3.65  
% 24.76/3.65  % (8713)Memory used [KB]: 29551
% 24.76/3.65  % (8713)Time elapsed: 2.368 s
% 24.76/3.65  % (8713)------------------------------
% 24.76/3.65  % (8713)------------------------------
% 24.76/3.65  % (8498)Time limit reached!
% 24.76/3.65  % (8498)------------------------------
% 24.76/3.65  % (8498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.76/3.65  % (8498)Termination reason: Time limit
% 24.76/3.65  % (8498)Termination phase: Saturation
% 24.76/3.65  
% 24.76/3.65  % (8498)Memory used [KB]: 23922
% 24.76/3.65  % (8498)Time elapsed: 3.0000 s
% 24.76/3.65  % (8498)------------------------------
% 24.76/3.65  % (8498)------------------------------
% 24.76/3.68  % (8763)Time limit reached!
% 24.76/3.68  % (8763)------------------------------
% 24.76/3.68  % (8763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.76/3.68  % (8763)Termination reason: Time limit
% 24.76/3.68  
% 24.76/3.68  % (8763)Memory used [KB]: 9466
% 24.76/3.68  % (8763)Time elapsed: 1.344 s
% 24.76/3.68  % (8763)------------------------------
% 24.76/3.68  % (8763)------------------------------
% 26.53/3.89  % (8653)Time limit reached!
% 26.53/3.89  % (8653)------------------------------
% 26.53/3.89  % (8653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.53/3.90  % (8653)Termination reason: Time limit
% 26.53/3.90  
% 26.53/3.90  % (8653)Memory used [KB]: 14839
% 26.53/3.90  % (8653)Time elapsed: 2.873 s
% 26.53/3.90  % (8653)------------------------------
% 26.53/3.90  % (8653)------------------------------
% 28.83/4.16  % (8756)Refutation found. Thanks to Tanya!
% 28.83/4.16  % SZS status Theorem for theBenchmark
% 28.83/4.16  % SZS output start Proof for theBenchmark
% 28.83/4.16  fof(f28877,plain,(
% 28.83/4.16    $false),
% 28.83/4.16    inference(unit_resulting_resolution,[],[f177,f27666,f2721])).
% 28.83/4.16  fof(f2721,plain,(
% 28.83/4.16    ( ! [X2,X3] : (m1_subset_1(k9_relat_1(sK3,X3),k1_zfmisc_1(X2)) | ~r1_tarski(k2_relat_1(sK3),X2)) )),
% 28.83/4.16    inference(subsumption_resolution,[],[f2711,f221])).
% 28.83/4.16  fof(f221,plain,(
% 28.83/4.16    ( ! [X2] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2))) | ~r1_tarski(k2_relat_1(sK3),X2)) )),
% 28.83/4.16    inference(resolution,[],[f155,f130])).
% 28.83/4.16  fof(f130,plain,(
% 28.83/4.16    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 28.83/4.16    inference(cnf_transformation,[],[f55])).
% 28.83/4.16  fof(f55,plain,(
% 28.83/4.16    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 28.83/4.16    inference(flattening,[],[f54])).
% 28.83/4.16  fof(f54,plain,(
% 28.83/4.16    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 28.83/4.16    inference(ennf_transformation,[],[f29])).
% 28.83/4.16  fof(f29,axiom,(
% 28.83/4.16    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 28.83/4.16  fof(f155,plain,(
% 28.83/4.16    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 28.83/4.16    inference(definition_unfolding,[],[f86,f153])).
% 28.83/4.16  fof(f153,plain,(
% 28.83/4.16    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 28.83/4.16    inference(definition_unfolding,[],[f91,f152])).
% 28.83/4.16  fof(f152,plain,(
% 28.83/4.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 28.83/4.16    inference(definition_unfolding,[],[f103,f151])).
% 28.83/4.16  fof(f151,plain,(
% 28.83/4.16    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 28.83/4.16    inference(definition_unfolding,[],[f120,f150])).
% 28.83/4.16  fof(f150,plain,(
% 28.83/4.16    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 28.83/4.16    inference(definition_unfolding,[],[f127,f149])).
% 28.83/4.16  fof(f149,plain,(
% 28.83/4.16    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 28.83/4.16    inference(definition_unfolding,[],[f133,f148])).
% 28.83/4.16  fof(f148,plain,(
% 28.83/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 28.83/4.16    inference(definition_unfolding,[],[f134,f147])).
% 28.83/4.16  fof(f147,plain,(
% 28.83/4.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 28.83/4.16    inference(cnf_transformation,[],[f10])).
% 28.83/4.16  fof(f10,axiom,(
% 28.83/4.16    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 28.83/4.16  fof(f134,plain,(
% 28.83/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 28.83/4.16    inference(cnf_transformation,[],[f9])).
% 28.83/4.16  fof(f9,axiom,(
% 28.83/4.16    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 28.83/4.16  fof(f133,plain,(
% 28.83/4.16    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 28.83/4.16    inference(cnf_transformation,[],[f8])).
% 28.83/4.16  fof(f8,axiom,(
% 28.83/4.16    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 28.83/4.16  fof(f127,plain,(
% 28.83/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 28.83/4.16    inference(cnf_transformation,[],[f7])).
% 28.83/4.16  fof(f7,axiom,(
% 28.83/4.16    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 28.83/4.16  fof(f120,plain,(
% 28.83/4.16    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 28.83/4.16    inference(cnf_transformation,[],[f6])).
% 28.83/4.16  fof(f6,axiom,(
% 28.83/4.16    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 28.83/4.16  fof(f103,plain,(
% 28.83/4.16    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 28.83/4.16    inference(cnf_transformation,[],[f5])).
% 28.83/4.16  fof(f5,axiom,(
% 28.83/4.16    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 28.83/4.16  fof(f91,plain,(
% 28.83/4.16    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 28.83/4.16    inference(cnf_transformation,[],[f4])).
% 28.83/4.16  fof(f4,axiom,(
% 28.83/4.16    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 28.83/4.16  fof(f86,plain,(
% 28.83/4.16    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 28.83/4.16    inference(cnf_transformation,[],[f62])).
% 28.83/4.16  fof(f62,plain,(
% 28.83/4.16    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 28.83/4.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f61])).
% 28.83/4.16  fof(f61,plain,(
% 28.83/4.16    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 28.83/4.16    introduced(choice_axiom,[])).
% 28.83/4.16  fof(f35,plain,(
% 28.83/4.16    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 28.83/4.16    inference(flattening,[],[f34])).
% 28.83/4.16  fof(f34,plain,(
% 28.83/4.16    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 28.83/4.16    inference(ennf_transformation,[],[f33])).
% 28.83/4.16  fof(f33,negated_conjecture,(
% 28.83/4.16    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 28.83/4.16    inference(negated_conjecture,[],[f32])).
% 28.83/4.16  fof(f32,conjecture,(
% 28.83/4.16    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 28.83/4.16  fof(f2711,plain,(
% 28.83/4.16    ( ! [X2,X3] : (m1_subset_1(k9_relat_1(sK3,X3),k1_zfmisc_1(X2)) | ~r1_tarski(k2_relat_1(sK3),X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2)))) )),
% 28.83/4.16    inference(superposition,[],[f650,f129])).
% 28.83/4.16  fof(f129,plain,(
% 28.83/4.16    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 28.83/4.16    inference(cnf_transformation,[],[f53])).
% 28.83/4.16  fof(f53,plain,(
% 28.83/4.16    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 28.83/4.16    inference(ennf_transformation,[],[f27])).
% 28.83/4.16  fof(f27,axiom,(
% 28.83/4.16    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 28.83/4.16  fof(f650,plain,(
% 28.83/4.16    ( ! [X6,X5] : (m1_subset_1(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X5,sK3,X6),k1_zfmisc_1(X5)) | ~r1_tarski(k2_relat_1(sK3),X5)) )),
% 28.83/4.16    inference(resolution,[],[f221,f128])).
% 28.83/4.16  fof(f128,plain,(
% 28.83/4.16    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 28.83/4.16    inference(cnf_transformation,[],[f52])).
% 28.83/4.16  fof(f52,plain,(
% 28.83/4.16    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 28.83/4.16    inference(ennf_transformation,[],[f25])).
% 28.83/4.16  fof(f25,axiom,(
% 28.83/4.16    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 28.83/4.16  fof(f27666,plain,(
% 28.83/4.16    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3)))),
% 28.83/4.16    inference(subsumption_resolution,[],[f27665,f114])).
% 28.83/4.16  fof(f114,plain,(
% 28.83/4.16    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 28.83/4.16    inference(cnf_transformation,[],[f76])).
% 28.83/4.16  fof(f76,plain,(
% 28.83/4.16    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 28.83/4.16    inference(nnf_transformation,[],[f15])).
% 28.83/4.16  fof(f15,axiom,(
% 28.83/4.16    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 28.83/4.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 28.83/4.16  fof(f27665,plain,(
% 28.83/4.16    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3))) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 28.83/4.16    inference(subsumption_resolution,[],[f27625,f14120])).
% 28.83/4.16  fof(f14120,plain,(
% 28.83/4.16    r2_hidden(sK0,k1_relat_1(sK3))),
% 28.83/4.16    inference(backward_demodulation,[],[f10636,f13974])).
% 28.83/4.16  fof(f13974,plain,(
% 28.83/4.16    sK0 = sK7(k1_relat_1(sK3),k1_xboole_0)),
% 28.83/4.16    inference(resolution,[],[f12944,f10636])).
% 28.83/4.16  fof(f12944,plain,(
% 28.83/4.16    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | sK0 = X0) )),
% 28.83/4.16    inference(duplicate_literal_removal,[],[f12916])).
% 28.83/4.16  fof(f12916,plain,(
% 28.83/4.16    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | sK0 = X0 | sK0 = X0 | sK0 = X0 | sK0 = X0 | sK0 = X0) )),
% 28.83/4.16    inference(resolution,[],[f1487,f190])).
% 28.83/4.16  fof(f190,plain,(
% 28.83/4.16    ( ! [X4,X2,X0,X7,X3,X1] : (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) )),
% 28.83/4.16    inference(equality_resolution,[],[f170])).
% 28.83/4.16  fof(f170,plain,(
% 28.83/4.16    ( ! [X4,X2,X0,X7,X5,X3,X1] : (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 28.83/4.16    inference(definition_unfolding,[],[f135,f149])).
% 28.83/4.16  fof(f135,plain,(
% 28.83/4.16    ( ! [X4,X2,X0,X7,X5,X3,X1] : (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 28.83/4.16    inference(cnf_transformation,[],[f83])).
% 28.83/4.16  fof(f83,plain,(
% 28.83/4.16    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | (((sK8(X0,X1,X2,X3,X4,X5) != X4 & sK8(X0,X1,X2,X3,X4,X5) != X3 & sK8(X0,X1,X2,X3,X4,X5) != X2 & sK8(X0,X1,X2,X3,X4,X5) != X1 & sK8(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5)) & (sK8(X0,X1,X2,X3,X4,X5) = X4 | sK8(X0,X1,X2,X3,X4,X5) = X3 | sK8(X0,X1,X2,X3,X4,X5) = X2 | sK8(X0,X1,X2,X3,X4,X5) = X1 | sK8(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 28.83/4.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f81,f82])).
% 28.83/4.16  fof(f82,plain,(
% 28.83/4.16    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5))) => (((sK8(X0,X1,X2,X3,X4,X5) != X4 & sK8(X0,X1,X2,X3,X4,X5) != X3 & sK8(X0,X1,X2,X3,X4,X5) != X2 & sK8(X0,X1,X2,X3,X4,X5) != X1 & sK8(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5)) & (sK8(X0,X1,X2,X3,X4,X5) = X4 | sK8(X0,X1,X2,X3,X4,X5) = X3 | sK8(X0,X1,X2,X3,X4,X5) = X2 | sK8(X0,X1,X2,X3,X4,X5) = X1 | sK8(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5))))),
% 28.83/4.16    introduced(choice_axiom,[])).
% 28.83/4.17  fof(f81,plain,(
% 28.83/4.17    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 28.83/4.17    inference(rectify,[],[f80])).
% 28.83/4.17  fof(f80,plain,(
% 28.83/4.17    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 28.83/4.17    inference(flattening,[],[f79])).
% 28.83/4.17  fof(f79,plain,(
% 28.83/4.17    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 28.83/4.17    inference(nnf_transformation,[],[f60])).
% 28.83/4.17  fof(f60,plain,(
% 28.83/4.17    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 28.83/4.17    inference(ennf_transformation,[],[f12])).
% 28.83/4.17  fof(f12,axiom,(
% 28.83/4.17    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 28.83/4.17  fof(f1487,plain,(
% 28.83/4.17    ( ! [X2] : (r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,k1_relat_1(sK3))) )),
% 28.83/4.17    inference(resolution,[],[f341,f111])).
% 28.83/4.17  fof(f111,plain,(
% 28.83/4.17    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 28.83/4.17    inference(cnf_transformation,[],[f75])).
% 28.83/4.17  fof(f75,plain,(
% 28.83/4.17    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 28.83/4.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f73,f74])).
% 28.83/4.17  fof(f74,plain,(
% 28.83/4.17    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 28.83/4.17    introduced(choice_axiom,[])).
% 28.83/4.17  fof(f73,plain,(
% 28.83/4.17    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 28.83/4.17    inference(rectify,[],[f72])).
% 28.83/4.17  fof(f72,plain,(
% 28.83/4.17    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 28.83/4.17    inference(nnf_transformation,[],[f45])).
% 28.83/4.17  fof(f45,plain,(
% 28.83/4.17    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 28.83/4.17    inference(ennf_transformation,[],[f1])).
% 28.83/4.17  fof(f1,axiom,(
% 28.83/4.17    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 28.83/4.17  fof(f341,plain,(
% 28.83/4.17    r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 28.83/4.17    inference(subsumption_resolution,[],[f333,f236])).
% 28.83/4.17  fof(f236,plain,(
% 28.83/4.17    v1_relat_1(sK3)),
% 28.83/4.17    inference(subsumption_resolution,[],[f227,f102])).
% 28.83/4.17  fof(f102,plain,(
% 28.83/4.17    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 28.83/4.17    inference(cnf_transformation,[],[f19])).
% 28.83/4.17  fof(f19,axiom,(
% 28.83/4.17    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 28.83/4.17  fof(f227,plain,(
% 28.83/4.17    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 28.83/4.17    inference(resolution,[],[f155,f92])).
% 28.83/4.17  fof(f92,plain,(
% 28.83/4.17    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 28.83/4.17    inference(cnf_transformation,[],[f36])).
% 28.83/4.17  fof(f36,plain,(
% 28.83/4.17    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 28.83/4.17    inference(ennf_transformation,[],[f17])).
% 28.83/4.17  fof(f17,axiom,(
% 28.83/4.17    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 28.83/4.17  fof(f333,plain,(
% 28.83/4.17    r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 28.83/4.17    inference(resolution,[],[f215,f104])).
% 28.83/4.17  fof(f104,plain,(
% 28.83/4.17    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 28.83/4.17    inference(cnf_transformation,[],[f69])).
% 28.83/4.17  fof(f69,plain,(
% 28.83/4.17    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 28.83/4.17    inference(nnf_transformation,[],[f41])).
% 28.83/4.17  fof(f41,plain,(
% 28.83/4.17    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 28.83/4.17    inference(ennf_transformation,[],[f18])).
% 28.83/4.17  fof(f18,axiom,(
% 28.83/4.17    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 28.83/4.17  fof(f215,plain,(
% 28.83/4.17    v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 28.83/4.17    inference(resolution,[],[f155,f122])).
% 28.83/4.17  fof(f122,plain,(
% 28.83/4.17    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 28.83/4.17    inference(cnf_transformation,[],[f48])).
% 28.83/4.17  fof(f48,plain,(
% 28.83/4.17    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 28.83/4.17    inference(ennf_transformation,[],[f24])).
% 28.83/4.17  fof(f24,axiom,(
% 28.83/4.17    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 28.83/4.17  fof(f10636,plain,(
% 28.83/4.17    r2_hidden(sK7(k1_relat_1(sK3),k1_xboole_0),k1_relat_1(sK3))),
% 28.83/4.17    inference(subsumption_resolution,[],[f1282,f10538])).
% 28.83/4.17  fof(f10538,plain,(
% 28.83/4.17    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 28.83/4.17    inference(duplicate_literal_removal,[],[f10537])).
% 28.83/4.17  fof(f10537,plain,(
% 28.83/4.17    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 28.83/4.17    inference(forward_demodulation,[],[f10536,f179])).
% 28.83/4.17  fof(f179,plain,(
% 28.83/4.17    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 28.83/4.17    inference(equality_resolution,[],[f117])).
% 28.83/4.17  fof(f117,plain,(
% 28.83/4.17    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 28.83/4.17    inference(cnf_transformation,[],[f78])).
% 28.83/4.17  fof(f78,plain,(
% 28.83/4.17    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 28.83/4.17    inference(flattening,[],[f77])).
% 28.83/4.17  fof(f77,plain,(
% 28.83/4.17    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 28.83/4.17    inference(nnf_transformation,[],[f11])).
% 28.83/4.17  fof(f11,axiom,(
% 28.83/4.17    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 28.83/4.17  fof(f10536,plain,(
% 28.83/4.17    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 28.83/4.17    inference(subsumption_resolution,[],[f10529,f10380])).
% 28.83/4.17  fof(f10380,plain,(
% 28.83/4.17    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 28.83/4.17    inference(resolution,[],[f9994,f1019])).
% 28.83/4.17  fof(f1019,plain,(
% 28.83/4.17    r2_hidden(sK6(sK3,sK2,sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),k1_relat_1(sK3))),
% 28.83/4.17    inference(subsumption_resolution,[],[f1018,f236])).
% 28.83/4.17  fof(f1018,plain,(
% 28.83/4.17    r2_hidden(sK6(sK3,sK2,sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 28.83/4.17    inference(subsumption_resolution,[],[f997,f84])).
% 28.83/4.17  fof(f84,plain,(
% 28.83/4.17    v1_funct_1(sK3)),
% 28.83/4.17    inference(cnf_transformation,[],[f62])).
% 28.83/4.17  fof(f997,plain,(
% 28.83/4.17    r2_hidden(sK6(sK3,sK2,sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 28.83/4.17    inference(resolution,[],[f600,f175])).
% 28.83/4.17  fof(f175,plain,(
% 28.83/4.17    ( ! [X6,X0,X1] : (r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 28.83/4.17    inference(equality_resolution,[],[f94])).
% 28.83/4.17  fof(f94,plain,(
% 28.83/4.17    ( ! [X6,X2,X0,X1] : (r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 28.83/4.17    inference(cnf_transformation,[],[f68])).
% 28.83/4.17  fof(f68,plain,(
% 28.83/4.17    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK4(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X1,X6)) = X6 & r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 28.83/4.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f64,f67,f66,f65])).
% 28.83/4.17  fof(f65,plain,(
% 28.83/4.17    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK4(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK4(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 28.83/4.17    introduced(choice_axiom,[])).
% 28.83/4.17  fof(f66,plain,(
% 28.83/4.17    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK4(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))))),
% 28.83/4.17    introduced(choice_axiom,[])).
% 28.83/4.17  fof(f67,plain,(
% 28.83/4.17    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X1,X6)) = X6 & r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))))),
% 28.83/4.17    introduced(choice_axiom,[])).
% 28.83/4.17  fof(f64,plain,(
% 28.83/4.17    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 28.83/4.17    inference(rectify,[],[f63])).
% 28.83/4.17  fof(f63,plain,(
% 28.83/4.17    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 28.83/4.17    inference(nnf_transformation,[],[f40])).
% 28.83/4.17  fof(f40,plain,(
% 28.83/4.17    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 28.83/4.17    inference(flattening,[],[f39])).
% 28.83/4.17  fof(f39,plain,(
% 28.83/4.17    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 28.83/4.17    inference(ennf_transformation,[],[f21])).
% 28.83/4.17  fof(f21,axiom,(
% 28.83/4.17    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 28.83/4.17  fof(f600,plain,(
% 28.83/4.17    r2_hidden(sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k9_relat_1(sK3,sK2))),
% 28.83/4.17    inference(resolution,[],[f566,f112])).
% 28.83/4.17  fof(f112,plain,(
% 28.83/4.17    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 28.83/4.17    inference(cnf_transformation,[],[f75])).
% 28.83/4.17  fof(f566,plain,(
% 28.83/4.17    ~r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 28.83/4.17    inference(backward_demodulation,[],[f154,f220])).
% 28.83/4.17  fof(f220,plain,(
% 28.83/4.17    ( ! [X1] : (k9_relat_1(sK3,X1) = k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X1)) )),
% 28.83/4.17    inference(resolution,[],[f155,f129])).
% 28.83/4.17  fof(f154,plain,(
% 28.83/4.17    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 28.83/4.17    inference(definition_unfolding,[],[f88,f153,f153])).
% 28.83/4.17  fof(f88,plain,(
% 28.83/4.17    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 28.83/4.17    inference(cnf_transformation,[],[f62])).
% 28.83/4.17  fof(f9994,plain,(
% 28.83/4.17    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,k1_xboole_0)) )),
% 28.83/4.17    inference(resolution,[],[f9964,f111])).
% 28.83/4.17  fof(f9964,plain,(
% 28.83/4.17    ( ! [X8] : (~r2_hidden(X8,k1_xboole_0)) )),
% 28.83/4.17    inference(resolution,[],[f2268,f89])).
% 28.83/4.17  fof(f89,plain,(
% 28.83/4.17    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 28.83/4.17    inference(cnf_transformation,[],[f3])).
% 28.83/4.17  fof(f3,axiom,(
% 28.83/4.17    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 28.83/4.17  fof(f2268,plain,(
% 28.83/4.17    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,X1)) )),
% 28.83/4.17    inference(resolution,[],[f2218,f111])).
% 28.83/4.17  fof(f2218,plain,(
% 28.83/4.17    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(k1_xboole_0))) )),
% 28.83/4.17    inference(resolution,[],[f2179,f119])).
% 28.83/4.17  fof(f119,plain,(
% 28.83/4.17    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 28.83/4.17    inference(cnf_transformation,[],[f46])).
% 28.83/4.17  fof(f46,plain,(
% 28.83/4.17    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 28.83/4.17    inference(ennf_transformation,[],[f23])).
% 28.83/4.17  fof(f23,axiom,(
% 28.83/4.17    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 28.83/4.17  fof(f2179,plain,(
% 28.83/4.17    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 28.83/4.17    inference(subsumption_resolution,[],[f2178,f90])).
% 28.83/4.17  fof(f90,plain,(
% 28.83/4.17    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 28.83/4.17    inference(cnf_transformation,[],[f13])).
% 28.83/4.17  fof(f13,axiom,(
% 28.83/4.17    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 28.83/4.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 28.83/4.17  fof(f2178,plain,(
% 28.83/4.17    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 28.83/4.17    inference(superposition,[],[f1364,f121])).
% 28.83/4.17  fof(f121,plain,(
% 28.83/4.17    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 28.83/4.17    inference(cnf_transformation,[],[f47])).
% 28.83/4.17  fof(f47,plain,(
% 28.83/4.17    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 28.83/4.17    inference(ennf_transformation,[],[f26])).
% 28.83/4.18  fof(f26,axiom,(
% 28.83/4.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 28.83/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 28.83/4.18  fof(f1364,plain,(
% 28.83/4.18    ( ! [X0,X1] : (r1_tarski(k1_relset_1(X0,X1,k1_xboole_0),X0)) )),
% 28.83/4.18    inference(subsumption_resolution,[],[f1363,f90])).
% 28.83/4.18  fof(f1363,plain,(
% 28.83/4.18    ( ! [X0,X1] : (r1_tarski(k1_relset_1(X0,X1,k1_xboole_0),X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 28.83/4.18    inference(superposition,[],[f316,f125])).
% 28.83/4.18  fof(f125,plain,(
% 28.83/4.18    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 28.83/4.18    inference(cnf_transformation,[],[f49])).
% 28.83/4.18  fof(f49,plain,(
% 28.83/4.18    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 28.83/4.18    inference(ennf_transformation,[],[f30])).
% 28.83/4.18  fof(f30,axiom,(
% 28.83/4.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 28.83/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 28.83/4.18  fof(f316,plain,(
% 28.83/4.18    ( ! [X12,X10,X11] : (r1_tarski(k8_relset_1(X10,X11,k1_xboole_0,X12),X10)) )),
% 28.83/4.18    inference(subsumption_resolution,[],[f308,f90])).
% 28.83/4.18  fof(f308,plain,(
% 28.83/4.18    ( ! [X12,X10,X11] : (r1_tarski(k8_relset_1(X10,X11,k1_xboole_0,X12),X10) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 28.83/4.18    inference(resolution,[],[f299,f132])).
% 28.83/4.18  fof(f132,plain,(
% 28.83/4.18    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 28.83/4.18    inference(cnf_transformation,[],[f59])).
% 28.83/4.18  fof(f59,plain,(
% 28.83/4.18    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))),
% 28.83/4.18    inference(flattening,[],[f58])).
% 28.83/4.18  fof(f58,plain,(
% 28.83/4.18    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)))),
% 28.83/4.18    inference(ennf_transformation,[],[f31])).
% 28.83/4.18  fof(f31,axiom,(
% 28.83/4.18    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 28.83/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).
% 28.83/4.18  fof(f299,plain,(
% 28.83/4.18    v1_funct_1(k1_xboole_0)),
% 28.83/4.18    inference(resolution,[],[f297,f90])).
% 28.83/4.18  fof(f297,plain,(
% 28.83/4.18    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK3)) | v1_funct_1(X0)) )),
% 28.83/4.18    inference(subsumption_resolution,[],[f191,f236])).
% 28.83/4.18  fof(f191,plain,(
% 28.83/4.18    ( ! [X0] : (v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK3)) | ~v1_relat_1(sK3)) )),
% 28.83/4.18    inference(resolution,[],[f84,f93])).
% 28.83/4.18  fof(f93,plain,(
% 28.83/4.18    ( ! [X0,X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 28.83/4.18    inference(cnf_transformation,[],[f38])).
% 28.83/4.18  fof(f38,plain,(
% 28.83/4.18    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 28.83/4.18    inference(flattening,[],[f37])).
% 28.83/4.18  fof(f37,plain,(
% 28.83/4.18    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 28.83/4.18    inference(ennf_transformation,[],[f20])).
% 28.83/4.18  fof(f20,axiom,(
% 28.83/4.18    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 28.83/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).
% 28.83/4.18  fof(f10529,plain,(
% 28.83/4.18    ( ! [X0] : (r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 28.83/4.18    inference(superposition,[],[f1540,f121])).
% 28.83/4.18  fof(f1540,plain,(
% 28.83/4.18    ( ! [X1] : (r1_tarski(k1_relset_1(k1_xboole_0,X1,sK3),k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))) )),
% 28.83/4.18    inference(superposition,[],[f353,f179])).
% 28.83/4.18  fof(f353,plain,(
% 28.83/4.18    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k1_relset_1(X0,X1,sK3),X0)) )),
% 28.83/4.18    inference(duplicate_literal_removal,[],[f352])).
% 28.83/4.18  fof(f352,plain,(
% 28.83/4.18    ( ! [X0,X1] : (r1_tarski(k1_relset_1(X0,X1,sK3),X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 28.83/4.18    inference(superposition,[],[f196,f125])).
% 28.83/4.18  fof(f196,plain,(
% 28.83/4.18    ( ! [X12,X10,X11] : (r1_tarski(k8_relset_1(X10,X11,sK3,X12),X10) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 28.83/4.18    inference(resolution,[],[f84,f132])).
% 28.83/4.18  fof(f1282,plain,(
% 28.83/4.18    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(sK7(k1_relat_1(sK3),k1_xboole_0),k1_relat_1(sK3))),
% 28.83/4.18    inference(resolution,[],[f331,f112])).
% 28.83/4.18  fof(f331,plain,(
% 28.83/4.18    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 28.83/4.18    inference(superposition,[],[f222,f179])).
% 28.83/4.18  fof(f222,plain,(
% 28.83/4.18    ( ! [X3] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) | ~r1_tarski(k1_relat_1(sK3),X3)) )),
% 28.83/4.18    inference(resolution,[],[f155,f131])).
% 28.83/4.18  fof(f131,plain,(
% 28.83/4.18    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 28.83/4.18    inference(cnf_transformation,[],[f57])).
% 28.83/4.18  fof(f57,plain,(
% 28.83/4.18    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 28.83/4.18    inference(flattening,[],[f56])).
% 28.83/4.18  fof(f56,plain,(
% 28.83/4.18    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 28.83/4.18    inference(ennf_transformation,[],[f28])).
% 28.83/4.18  fof(f28,axiom,(
% 28.83/4.18    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 28.83/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 28.83/4.18  fof(f27625,plain,(
% 28.83/4.18    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3))) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 28.83/4.18    inference(trivial_inequality_removal,[],[f27538])).
% 28.83/4.18  fof(f27538,plain,(
% 28.83/4.18    sK0 != sK0 | ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3))) | k1_relat_1(sK3) != k1_relat_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 28.83/4.18    inference(superposition,[],[f2566,f27482])).
% 28.83/4.18  fof(f27482,plain,(
% 28.83/4.18    sK0 = sK8(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK3)) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 28.83/4.18    inference(subsumption_resolution,[],[f4572,f12944])).
% 28.83/4.18  fof(f4572,plain,(
% 28.83/4.18    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK3)) | r2_hidden(sK8(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK3)),k1_relat_1(sK3))),
% 28.83/4.18    inference(equality_resolution,[],[f729])).
% 28.83/4.18  fof(f729,plain,(
% 28.83/4.18    ( ! [X0] : (k1_relat_1(sK3) != X0 | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0) | r2_hidden(sK8(sK0,sK0,sK0,sK0,sK0,X0),X0)) )),
% 28.83/4.18    inference(duplicate_literal_removal,[],[f723])).
% 28.83/4.18  fof(f723,plain,(
% 28.83/4.18    ( ! [X0] : (k1_relat_1(sK3) != X0 | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0) | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0) | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0) | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0) | sK0 = sK8(sK0,sK0,sK0,sK0,sK0,X0) | r2_hidden(sK8(sK0,sK0,sK0,sK0,sK0,X0),X0)) )),
% 28.83/4.18    inference(superposition,[],[f623,f164])).
% 28.83/4.18  fof(f164,plain,(
% 28.83/4.18    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = X5 | sK8(X0,X1,X2,X3,X4,X5) = X4 | sK8(X0,X1,X2,X3,X4,X5) = X3 | sK8(X0,X1,X2,X3,X4,X5) = X2 | sK8(X0,X1,X2,X3,X4,X5) = X1 | sK8(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5)) )),
% 28.83/4.18    inference(definition_unfolding,[],[f141,f149])).
% 28.83/4.18  fof(f141,plain,(
% 28.83/4.18    ( ! [X4,X2,X0,X5,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 | sK8(X0,X1,X2,X3,X4,X5) = X4 | sK8(X0,X1,X2,X3,X4,X5) = X3 | sK8(X0,X1,X2,X3,X4,X5) = X2 | sK8(X0,X1,X2,X3,X4,X5) = X1 | sK8(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5)) )),
% 28.83/4.18    inference(cnf_transformation,[],[f83])).
% 28.83/4.18  fof(f623,plain,(
% 28.83/4.18    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 28.83/4.18    inference(subsumption_resolution,[],[f622,f236])).
% 28.83/4.18  fof(f622,plain,(
% 28.83/4.18    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 28.83/4.18    inference(subsumption_resolution,[],[f606,f84])).
% 28.83/4.18  fof(f606,plain,(
% 28.83/4.18    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 28.83/4.18    inference(superposition,[],[f566,f158])).
% 28.83/4.18  fof(f158,plain,(
% 28.83/4.18    ( ! [X0,X1] : (k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | k1_relat_1(X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 28.83/4.18    inference(definition_unfolding,[],[f107,f153,f153])).
% 28.83/4.18  fof(f107,plain,(
% 28.83/4.18    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 28.83/4.18    inference(cnf_transformation,[],[f44])).
% 28.83/4.18  fof(f44,plain,(
% 28.83/4.18    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 28.83/4.18    inference(flattening,[],[f43])).
% 28.83/4.18  fof(f43,plain,(
% 28.83/4.18    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 28.83/4.18    inference(ennf_transformation,[],[f22])).
% 28.83/4.18  fof(f22,axiom,(
% 28.83/4.18    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 28.83/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 28.83/4.18  fof(f2566,plain,(
% 28.83/4.18    ( ! [X1] : (sK0 != sK8(sK0,sK0,sK0,sK0,sK0,X1) | ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3))) | k1_relat_1(sK3) != X1 | ~r2_hidden(sK0,X1)) )),
% 28.83/4.18    inference(inner_rewriting,[],[f2560])).
% 28.83/4.18  fof(f2560,plain,(
% 28.83/4.18    ( ! [X1] : (k1_relat_1(sK3) != X1 | ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3))) | sK0 != sK8(sK0,sK0,sK0,sK0,sK0,X1) | ~r2_hidden(sK8(sK0,sK0,sK0,sK0,sK0,X1),X1)) )),
% 28.83/4.18    inference(superposition,[],[f967,f163])).
% 28.83/4.18  fof(f163,plain,(
% 28.83/4.18    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = X5 | sK8(X0,X1,X2,X3,X4,X5) != X0 | ~r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5)) )),
% 28.83/4.18    inference(definition_unfolding,[],[f142,f149])).
% 28.83/4.18  fof(f142,plain,(
% 28.83/4.18    ( ! [X4,X2,X0,X5,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 | sK8(X0,X1,X2,X3,X4,X5) != X0 | ~r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5)) )),
% 28.83/4.18    inference(cnf_transformation,[],[f83])).
% 28.83/4.18  fof(f967,plain,(
% 28.83/4.18    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3)))),
% 28.83/4.18    inference(subsumption_resolution,[],[f966,f236])).
% 28.83/4.18  fof(f966,plain,(
% 28.83/4.18    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3))) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 28.83/4.18    inference(subsumption_resolution,[],[f950,f84])).
% 28.83/4.18  fof(f950,plain,(
% 28.83/4.18    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_relat_1(sK3))) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 28.83/4.18    inference(superposition,[],[f599,f158])).
% 28.83/4.18  fof(f599,plain,(
% 28.83/4.18    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))))),
% 28.83/4.18    inference(resolution,[],[f566,f114])).
% 28.83/4.18  fof(f177,plain,(
% 28.83/4.18    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 28.83/4.18    inference(equality_resolution,[],[f108])).
% 28.83/4.18  fof(f108,plain,(
% 28.83/4.18    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 28.83/4.18    inference(cnf_transformation,[],[f71])).
% 28.83/4.18  fof(f71,plain,(
% 28.83/4.18    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 28.83/4.18    inference(flattening,[],[f70])).
% 28.83/4.18  fof(f70,plain,(
% 28.83/4.18    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 28.83/4.18    inference(nnf_transformation,[],[f2])).
% 28.83/4.18  fof(f2,axiom,(
% 28.83/4.18    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 28.83/4.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 28.83/4.18  % SZS output end Proof for theBenchmark
% 28.83/4.18  % (8756)------------------------------
% 28.83/4.18  % (8756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.83/4.18  % (8756)Termination reason: Refutation
% 28.83/4.18  
% 28.83/4.18  % (8756)Memory used [KB]: 20724
% 28.83/4.18  % (8756)Time elapsed: 2.595 s
% 28.83/4.18  % (8756)------------------------------
% 28.83/4.18  % (8756)------------------------------
% 28.83/4.18  % (8315)Success in time 3.819 s
%------------------------------------------------------------------------------
