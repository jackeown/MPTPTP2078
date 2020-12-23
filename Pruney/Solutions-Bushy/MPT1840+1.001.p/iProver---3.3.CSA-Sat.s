%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1840+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:37 EST 2020

% Result     : CounterSatisfiable 0.56s
% Output     : Saturation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   23 (  37 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 154 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( ( v7_struct_0(X0)
              & u1_struct_0(X0) = u1_struct_0(X1) )
           => v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ( ( v7_struct_0(X0)
                & u1_struct_0(X0) = u1_struct_0(X1) )
             => v7_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
     => ( ~ v7_struct_0(sK1)
        & v7_struct_0(X0)
        & u1_struct_0(sK1) = u1_struct_0(X0)
        & l1_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v7_struct_0(X1)
            & v7_struct_0(X0)
            & u1_struct_0(X0) = u1_struct_0(X1)
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(sK0)
          & u1_struct_0(sK0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ v7_struct_0(sK1)
    & v7_struct_0(sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12,f11])).

fof(f18,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ~ v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_79,plain,
    ( u1_struct_0(X0_34) = u1_struct_0(X1_34)
    | X0_34 != X1_34 ),
    theory(equality)).

cnf(c_78,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_76,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_4,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_74,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_57,plain,
    ( ~ v7_struct_0(X0)
    | v7_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_56,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_55,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_51,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_2,negated_conjecture,
    ( ~ v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,negated_conjecture,
    ( v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_65,plain,
    ( sK0 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_73,plain,
    ( sK0 != sK1 ),
    inference(subtyping,[status(esa)],[c_65])).


%------------------------------------------------------------------------------
