%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2004+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:01 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   18 (  42 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 ( 195 expanded)
%              Number of equality atoms :   24 (  78 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                      & X2 = X3
                      & u1_struct_0(X0) = u1_struct_0(X1) )
                   => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                        & X2 = X3
                        & u1_struct_0(X0) = u1_struct_0(X1) )
                     => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f3,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2,X3] :
                ( ( m1_setfam_1(X2,u1_struct_0(X0))
                  & X2 = X3
                  & u1_struct_0(X0) = u1_struct_0(X1) )
               => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f4,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_setfam_1(X2,u1_struct_0(X0))
          & X2 = X3
          & u1_struct_0(X0) = u1_struct_0(X1) )
       => m1_setfam_1(X3,u1_struct_0(X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_setfam_1(X3,u1_struct_0(X1))
      & m1_setfam_1(X2,u1_struct_0(X0))
      & X2 = X3
      & u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_setfam_1(X3,u1_struct_0(X1))
      & m1_setfam_1(X2,u1_struct_0(X0))
      & X2 = X3
      & u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(flattening,[],[f5])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_setfam_1(X3,u1_struct_0(X1))
        & m1_setfam_1(X2,u1_struct_0(X0))
        & X2 = X3
        & u1_struct_0(X0) = u1_struct_0(X1) )
   => ( ~ m1_setfam_1(sK3,u1_struct_0(sK1))
      & m1_setfam_1(sK2,u1_struct_0(sK0))
      & sK2 = sK3
      & u1_struct_0(sK0) = u1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ~ m1_setfam_1(sK3,u1_struct_0(sK1))
    & m1_setfam_1(sK2,u1_struct_0(sK0))
    & sK2 = sK3
    & u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f12,plain,(
    ~ m1_setfam_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,plain,(
    m1_setfam_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f9,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_0,negated_conjecture,
    ( ~ m1_setfam_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,negated_conjecture,
    ( m1_setfam_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_25,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | sK2 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_2,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_3,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25,c_2,c_3])).


%------------------------------------------------------------------------------
