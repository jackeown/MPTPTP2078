%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1082+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:51 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 ( 240 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
              | ~ m1_subset_1(X3,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK0(X0,X1,X2),X0,X1)
          | ~ v1_funct_1(sK0(X0,X1,X2)) )
        & m1_subset_1(sK0(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ( ( ~ m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(sK0(X0,X1,X2),X0,X1)
              | ~ v1_funct_1(sK0(X0,X1,X2)) )
            & m1_subset_1(sK0(X0,X1,X2),X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK0(X0,X1,X2),X0,X1)
      | ~ v1_funct_1(sK0(X0,X1,X2))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),X2)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
        & ~ v1_xboole_0(X1) )
   => ( ~ m1_funct_2(k1_funct_2(sK1,sK2),sK1,sK2)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ m1_funct_2(k1_funct_2(sK1,sK2),sK1,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f17])).

fof(f30,plain,(
    ~ m1_funct_2(k1_funct_2(sK1,sK2),sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_367,plain,
    ( r2_hidden(X0_42,X0_40)
    | ~ m1_subset_1(X0_42,X0_40)
    | v1_xboole_0(X0_40) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_432,plain,
    ( r2_hidden(sK0(sK1,sK2,k1_funct_2(sK1,sK2)),k1_funct_2(sK1,sK2))
    | ~ m1_subset_1(sK0(sK1,sK2,k1_funct_2(sK1,sK2)),k1_funct_2(sK1,sK2))
    | v1_xboole_0(k1_funct_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_0,plain,
    ( ~ v1_funct_2(sK0(X0,X1,X2),X0,X1)
    | m1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(sK0(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k1_funct_2(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_183,plain,
    ( m1_funct_2(X0,X1,X2)
    | ~ r2_hidden(sK0(X1,X2,X0),k1_funct_2(X1,X2))
    | ~ m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X0)
    | ~ v1_funct_1(sK0(X1,X2,X0)) ),
    inference(resolution,[status(thm)],[c_0,c_7])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_197,plain,
    ( m1_funct_2(X0,X1,X2)
    | ~ r2_hidden(sK0(X1,X2,X0),k1_funct_2(X1,X2))
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_183,c_8,c_6])).

cnf(c_364,plain,
    ( m1_funct_2(X0_40,X0_41,X1_40)
    | ~ r2_hidden(sK0(X0_41,X1_40,X0_40),k1_funct_2(X0_41,X1_40))
    | v1_xboole_0(X0_40) ),
    inference(subtyping,[status(esa)],[c_197])).

cnf(c_423,plain,
    ( m1_funct_2(k1_funct_2(sK1,sK2),sK1,sK2)
    | ~ r2_hidden(sK0(sK1,sK2,k1_funct_2(sK1,sK2)),k1_funct_2(sK1,sK2))
    | v1_xboole_0(k1_funct_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_1,plain,
    ( m1_funct_2(X0,X1,X2)
    | m1_subset_1(sK0(X1,X2,X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_371,plain,
    ( m1_funct_2(X0_40,X0_41,X1_40)
    | m1_subset_1(sK0(X0_41,X1_40,X0_40),X0_40)
    | v1_xboole_0(X0_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_420,plain,
    ( m1_funct_2(k1_funct_2(sK1,sK2),sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2,k1_funct_2(sK1,sK2)),k1_funct_2(sK1,sK2))
    | v1_xboole_0(k1_funct_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_5,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_369,plain,
    ( v1_xboole_0(X0_40)
    | ~ v1_xboole_0(k1_funct_2(X0_41,X0_40)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_379,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,sK2))
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_10,negated_conjecture,
    ( ~ m1_funct_2(k1_funct_2(sK1,sK2),sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_432,c_423,c_420,c_379,c_10,c_11])).


%------------------------------------------------------------------------------
