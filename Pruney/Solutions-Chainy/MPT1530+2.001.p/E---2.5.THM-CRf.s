%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:13 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  109 (5064415 expanded)
%              Number of clauses        :  100 (2121810 expanded)
%              Number of leaves         :    4 (1131324 expanded)
%              Depth                    :   47
%              Number of atoms          :  589 (163260355 expanded)
%              Number of equality atoms :  122 (4816607 expanded)
%              Maximal formula depth    :   46 (   5 average)
%              Maximal clause size      :  184 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
                     => ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X2,X4) ) )
                    & ( ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X2,X4) )
                     => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
                    & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
                     => ( r1_orders_2(X1,X3,X2)
                        & r1_orders_2(X1,X4,X2) ) )
                    & ( ( r1_orders_2(X1,X3,X2)
                        & r1_orders_2(X1,X4,X2) )
                     => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
                       => ( r1_orders_2(X1,X2,X3)
                          & r1_orders_2(X1,X2,X4) ) )
                      & ( ( r1_orders_2(X1,X2,X3)
                          & r1_orders_2(X1,X2,X4) )
                       => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
                      & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
                       => ( r1_orders_2(X1,X3,X2)
                          & r1_orders_2(X1,X4,X2) ) )
                      & ( ( r1_orders_2(X1,X3,X2)
                          & r1_orders_2(X1,X4,X2) )
                       => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_yellow_0])).

fof(c_0_5,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r2_hidden(X22,X20)
        | r1_orders_2(X19,X22,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( m1_subset_1(esk3_3(X19,X20,X21),u1_struct_0(X19))
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( r2_hidden(esk3_3(X19,X20,X21),X20)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r1_orders_2(X19,esk3_3(X19,X20,X21),X21)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_6,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk7_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,X16,esk2_3(X14,X15,X16))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_9,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).

cnf(c_0_16,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_10]),c_0_11])])).

cnf(c_0_17,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk7_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_19]),c_0_11])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,X1)
    | ~ r2_lattice3(esk4_0,k2_tarski(X2,esk7_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ r1_orders_2(esk4_0,esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk5_0)
    | ~ r2_lattice3(esk4_0,k2_tarski(X1,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_35,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | r2_hidden(esk3_3(esk4_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_11])])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk7_0)
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk7_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_19]),c_0_11])])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk5_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_11])])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(X1,X2),esk5_0) = X2
    | esk3_3(esk4_0,k2_tarski(X1,X2),esk5_0) = X1
    | r2_lattice3(esk4_0,k2_tarski(X1,X2),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk7_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(X2,esk7_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(X1,X2),esk5_0) = X2
    | esk2_3(esk4_0,k2_tarski(X1,X2),esk5_0) = X1
    | r1_lattice3(esk4_0,k2_tarski(X1,X2),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ r1_orders_2(esk4_0,esk7_0,esk5_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_44,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk7_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(X1,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_42])).

cnf(c_0_47,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_48,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34]),c_0_22]),c_0_45]),c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk5_0)
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_50,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_46]),c_0_34]),c_0_22]),c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk3_3(esk4_0,X1,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_18]),c_0_11])])).

cnf(c_0_52,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | r1_orders_2(esk4_0,esk7_0,esk5_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_45]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | r1_orders_2(esk4_0,esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_58,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X2),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | esk2_3(esk4_0,k2_tarski(esk6_0,X2),esk5_0) = X2 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_56]),c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_46]),c_0_45]),c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1 ),
    inference(ef,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_42])).

cnf(c_0_62,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_60]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk7_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_64,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X2),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1
    | esk2_3(esk4_0,k2_tarski(esk6_0,X2),esk5_0) = X2 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_62]),c_0_42])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk7_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_63])).

cnf(c_0_66,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_67,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0) = X1 ),
    inference(ef,[status(thm)],[c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk7_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ r1_orders_2(esk4_0,esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_69,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,X1,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_18]),c_0_11])])).

cnf(c_0_71,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0 ),
    inference(ef,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk7_0)
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_34]),c_0_45])).

cnf(c_0_73,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_40])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk5_0)
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk7_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_76,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_48])).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk7_0)
    | r1_orders_2(esk4_0,esk7_0,esk5_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_82]),c_0_73]),c_0_34]),c_0_22]),c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_82]),c_0_73]),c_0_80]),c_0_78]),c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_69]),c_0_72])).

cnf(c_0_87,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_88]),c_0_87]),c_0_34]),c_0_22]),c_0_72])).

cnf(c_0_90,negated_conjecture,
    ( esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_88]),c_0_87]),c_0_86]),c_0_85]),c_0_89])).

cnf(c_0_91,negated_conjecture,
    ( r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk5_0)
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_93,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk7_0
    | esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_44]),c_0_48])).

cnf(c_0_94,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk7_0,esk5_0)
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_39])).

cnf(c_0_98,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_97])).

cnf(c_0_99,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_79]),c_0_72])).

cnf(c_0_100,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0
    | ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_97]),c_0_98]),c_0_34]),c_0_22]),c_0_72])).

cnf(c_0_101,negated_conjecture,
    ( esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_97]),c_0_98]),c_0_99]),c_0_95]),c_0_100])).

cnf(c_0_102,negated_conjecture,
    ( r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_101])).

cnf(c_0_103,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_33]),c_0_39])).

cnf(c_0_104,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_69]),c_0_72])).

cnf(c_0_105,negated_conjecture,
    ( r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_103])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_104])]),c_0_103]),c_0_105])]),c_0_34]),c_0_22])).

cnf(c_0_107,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_104])]),c_0_103]),c_0_105])]),c_0_106])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_107])]),c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 6.02/6.26  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 6.02/6.26  # and selection function SelectNewComplexAHP.
% 6.02/6.26  #
% 6.02/6.26  # Preprocessing time       : 0.028 s
% 6.02/6.26  # Presaturation interreduction done
% 6.02/6.26  
% 6.02/6.26  # Proof found!
% 6.02/6.26  # SZS status Theorem
% 6.02/6.26  # SZS output start CNFRefutation
% 6.02/6.26  fof(t8_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_yellow_0)).
% 6.02/6.26  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 6.02/6.26  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.02/6.26  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 6.02/6.26  fof(c_0_4, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2)))))))), inference(assume_negation,[status(cth)],[t8_yellow_0])).
% 6.02/6.26  fof(c_0_5, plain, ![X19, X20, X21, X22]:((~r2_lattice3(X19,X20,X21)|(~m1_subset_1(X22,u1_struct_0(X19))|(~r2_hidden(X22,X20)|r1_orders_2(X19,X22,X21)))|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&((m1_subset_1(esk3_3(X19,X20,X21),u1_struct_0(X19))|r2_lattice3(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&((r2_hidden(esk3_3(X19,X20,X21),X20)|r2_lattice3(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&(~r1_orders_2(X19,esk3_3(X19,X20,X21),X21)|r2_lattice3(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 6.02/6.26  fof(c_0_6, negated_conjecture, (l1_orders_2(esk4_0)&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(((((((r1_orders_2(esk4_0,esk6_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))&(((r1_orders_2(esk4_0,esk6_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0))))))&((((r1_orders_2(esk4_0,esk6_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))&(((r1_orders_2(esk4_0,esk6_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))))&((((r1_orders_2(esk4_0,esk6_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))&(((r1_orders_2(esk4_0,esk6_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)))))))&((((((r1_orders_2(esk4_0,esk6_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))&(((r1_orders_2(esk4_0,esk6_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk6_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)))))))&((((r1_orders_2(esk4_0,esk6_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))&(((r1_orders_2(esk4_0,esk6_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(r1_orders_2(esk4_0,esk5_0,esk7_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))))&((((r1_orders_2(esk4_0,esk6_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))&(((r1_orders_2(esk4_0,esk6_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)))))&(r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))&(~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|(~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|(~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 6.02/6.26  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 6.02/6.26  fof(c_0_8, plain, ![X14, X15, X16, X17]:((~r1_lattice3(X14,X15,X16)|(~m1_subset_1(X17,u1_struct_0(X14))|(~r2_hidden(X17,X15)|r1_orders_2(X14,X16,X17)))|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((r2_hidden(esk2_3(X14,X15,X16),X15)|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&(~r1_orders_2(X14,X16,esk2_3(X14,X15,X16))|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 6.02/6.26  cnf(c_0_9, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 6.02/6.26  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_12, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 6.02/6.26  cnf(c_0_13, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 6.02/6.26  cnf(c_0_14, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,X1)|~r2_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk6_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 6.02/6.26  cnf(c_0_15, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).
% 6.02/6.26  cnf(c_0_16, negated_conjecture, (r1_orders_2(esk4_0,X1,esk6_0)|~r1_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk6_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_10]), c_0_11])])).
% 6.02/6.26  cnf(c_0_17, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,X1)|~r2_lattice3(esk4_0,k2_tarski(esk6_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 6.02/6.26  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 6.02/6.26  cnf(c_0_21, negated_conjecture, (r1_orders_2(esk4_0,X1,esk6_0)|~r1_lattice3(esk4_0,k2_tarski(esk6_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 6.02/6.26  cnf(c_0_22, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,esk5_0)|~r2_lattice3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 6.02/6.26  cnf(c_0_23, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,esk5_0)|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_24, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,X1)|~r2_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk7_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_19]), c_0_11])])).
% 6.02/6.26  cnf(c_0_25, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).
% 6.02/6.26  cnf(c_0_26, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 6.02/6.26  cnf(c_0_27, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_orders_2(esk4_0,esk6_0,esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 6.02/6.26  cnf(c_0_28, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,X1)|~r2_lattice3(esk4_0,k2_tarski(X2,esk7_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 6.02/6.26  cnf(c_0_29, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 6.02/6.26  cnf(c_0_30, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 6.02/6.26  cnf(c_0_31, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 6.02/6.26  cnf(c_0_32, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_33, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,esk5_0)|r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 6.02/6.26  cnf(c_0_34, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,esk5_0)|~r2_lattice3(esk4_0,k2_tarski(X1,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 6.02/6.26  cnf(c_0_35, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_29])).
% 6.02/6.26  cnf(c_0_36, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|r2_hidden(esk3_3(esk4_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_18]), c_0_11])])).
% 6.02/6.26  cnf(c_0_37, negated_conjecture, (r1_orders_2(esk4_0,X1,esk7_0)|~r1_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk7_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_19]), c_0_11])])).
% 6.02/6.26  cnf(c_0_38, negated_conjecture, (r1_lattice3(esk4_0,X1,esk5_0)|r2_hidden(esk2_3(esk4_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_11])])).
% 6.02/6.26  cnf(c_0_39, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_26])).
% 6.02/6.26  cnf(c_0_40, negated_conjecture, (esk3_3(esk4_0,k2_tarski(X1,X2),esk5_0)=X2|esk3_3(esk4_0,k2_tarski(X1,X2),esk5_0)=X1|r2_lattice3(esk4_0,k2_tarski(X1,X2),esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 6.02/6.26  cnf(c_0_41, negated_conjecture, (r1_orders_2(esk4_0,X1,esk7_0)|~r1_lattice3(esk4_0,k2_tarski(X2,esk7_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_25])).
% 6.02/6.26  cnf(c_0_42, negated_conjecture, (esk2_3(esk4_0,k2_tarski(X1,X2),esk5_0)=X2|esk2_3(esk4_0,k2_tarski(X1,X2),esk5_0)=X1|r1_lattice3(esk4_0,k2_tarski(X1,X2),esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_38])).
% 6.02/6.26  cnf(c_0_43, negated_conjecture, (~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)|~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_44, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 6.02/6.26  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk4_0,k2_tarski(X1,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_18])).
% 6.02/6.26  cnf(c_0_46, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_42])).
% 6.02/6.26  cnf(c_0_47, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 6.02/6.26  cnf(c_0_48, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_34]), c_0_22]), c_0_45]), c_0_40])).
% 6.02/6.26  cnf(c_0_49, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,esk5_0)|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_50, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_46]), c_0_34]), c_0_22]), c_0_45])).
% 6.02/6.26  cnf(c_0_51, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|~r1_orders_2(esk4_0,esk3_3(esk4_0,X1,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_18]), c_0_11])])).
% 6.02/6.26  cnf(c_0_52, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0), inference(spm,[status(thm)],[c_0_48, c_0_42])).
% 6.02/6.26  cnf(c_0_53, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|r1_orders_2(esk4_0,esk7_0,esk5_0)|~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_46]), c_0_45]), c_0_50])).
% 6.02/6.26  cnf(c_0_54, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 6.02/6.26  cnf(c_0_55, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|r1_orders_2(esk4_0,esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_53, c_0_42])).
% 6.02/6.26  cnf(c_0_56, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 6.02/6.26  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,esk5_0)|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk5_0,esk6_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_58, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X2),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|esk2_3(esk4_0,k2_tarski(esk6_0,X2),esk5_0)=X2), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_56]), c_0_42])).
% 6.02/6.26  cnf(c_0_59, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_46]), c_0_45]), c_0_50])).
% 6.02/6.26  cnf(c_0_60, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1), inference(ef,[status(thm)],[c_0_58])).
% 6.02/6.26  cnf(c_0_61, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|r1_orders_2(esk4_0,esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_42])).
% 6.02/6.26  cnf(c_0_62, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_60]), c_0_61])).
% 6.02/6.26  cnf(c_0_63, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,esk5_0)|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_64, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X2),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1|esk2_3(esk4_0,k2_tarski(esk6_0,X2),esk5_0)=X2), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_62]), c_0_42])).
% 6.02/6.26  cnf(c_0_65, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_orders_2(esk4_0,esk6_0,esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_63])).
% 6.02/6.26  cnf(c_0_66, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 6.02/6.26  cnf(c_0_67, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,X1),esk5_0)=X1), inference(ef,[status(thm)],[c_0_64])).
% 6.02/6.26  cnf(c_0_68, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk6_0,esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_69, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,esk5_0)|r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_65])).
% 6.02/6.26  cnf(c_0_70, negated_conjecture, (r1_lattice3(esk4_0,X1,esk5_0)|~r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,X1,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_18]), c_0_11])])).
% 6.02/6.26  cnf(c_0_71, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0), inference(ef,[status(thm)],[c_0_67])).
% 6.02/6.26  cnf(c_0_72, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk7_0)|~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_34]), c_0_45])).
% 6.02/6.26  cnf(c_0_73, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 6.02/6.26  cnf(c_0_74, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_72, c_0_40])).
% 6.02/6.26  cnf(c_0_75, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,esk5_0)|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_76, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_48])).
% 6.02/6.26  cnf(c_0_77, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk7_0)|r1_orders_2(esk4_0,esk7_0,esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_75])).
% 6.02/6.26  cnf(c_0_78, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_76])).
% 6.02/6.26  cnf(c_0_79, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,esk5_0)|r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_77])).
% 6.02/6.26  cnf(c_0_80, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_72])).
% 6.02/6.26  cnf(c_0_81, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_80])).
% 6.02/6.26  cnf(c_0_82, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_81])).
% 6.02/6.26  cnf(c_0_83, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_82]), c_0_73]), c_0_34]), c_0_22]), c_0_72])).
% 6.02/6.26  cnf(c_0_84, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_82]), c_0_73]), c_0_80]), c_0_78]), c_0_83])).
% 6.02/6.26  cnf(c_0_85, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_84])).
% 6.02/6.26  cnf(c_0_86, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_69]), c_0_72])).
% 6.02/6.26  cnf(c_0_87, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_86])).
% 6.02/6.26  cnf(c_0_88, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_87])).
% 6.02/6.26  cnf(c_0_89, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_88]), c_0_87]), c_0_34]), c_0_22]), c_0_72])).
% 6.02/6.26  cnf(c_0_90, negated_conjecture, (esk2_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_88]), c_0_87]), c_0_86]), c_0_85]), c_0_89])).
% 6.02/6.26  cnf(c_0_91, negated_conjecture, (r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_70, c_0_90])).
% 6.02/6.26  cnf(c_0_92, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,esk5_0)|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 6.02/6.26  cnf(c_0_93, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk7_0|esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_44]), c_0_48])).
% 6.02/6.26  cnf(c_0_94, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk6_0)|r1_orders_2(esk4_0,esk7_0,esk5_0)|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_92])).
% 6.02/6.26  cnf(c_0_95, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_93])).
% 6.02/6.26  cnf(c_0_96, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,esk5_0)|r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_94])).
% 6.02/6.26  cnf(c_0_97, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_39])).
% 6.02/6.26  cnf(c_0_98, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_91, c_0_97])).
% 6.02/6.26  cnf(c_0_99, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_79]), c_0_72])).
% 6.02/6.26  cnf(c_0_100, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0|~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_97]), c_0_98]), c_0_34]), c_0_22]), c_0_72])).
% 6.02/6.26  cnf(c_0_101, negated_conjecture, (esk3_3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_97]), c_0_98]), c_0_99]), c_0_95]), c_0_100])).
% 6.02/6.26  cnf(c_0_102, negated_conjecture, (r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)|~r1_orders_2(esk4_0,esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_101])).
% 6.02/6.26  cnf(c_0_103, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_33]), c_0_39])).
% 6.02/6.26  cnf(c_0_104, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_69]), c_0_72])).
% 6.02/6.26  cnf(c_0_105, negated_conjecture, (r1_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_103])])).
% 6.02/6.26  cnf(c_0_106, negated_conjecture, (~r2_lattice3(esk4_0,k2_tarski(esk6_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_104])]), c_0_103]), c_0_105])]), c_0_34]), c_0_22])).
% 6.02/6.26  cnf(c_0_107, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_104])]), c_0_103]), c_0_105])]), c_0_106])).
% 6.02/6.26  cnf(c_0_108, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_107])]), c_0_106]), ['proof']).
% 6.02/6.26  # SZS output end CNFRefutation
% 6.02/6.26  # Proof object total steps             : 109
% 6.02/6.26  # Proof object clause steps            : 100
% 6.02/6.26  # Proof object formula steps           : 9
% 6.02/6.26  # Proof object conjectures             : 91
% 6.02/6.26  # Proof object clause conjectures      : 88
% 6.02/6.26  # Proof object formula conjectures     : 3
% 6.02/6.26  # Proof object initial clauses used    : 22
% 6.02/6.26  # Proof object initial formulas used   : 4
% 6.02/6.26  # Proof object generating inferences   : 71
% 6.02/6.26  # Proof object simplifying inferences  : 89
% 6.02/6.26  # Training examples: 0 positive, 0 negative
% 6.02/6.26  # Parsed axioms                        : 4
% 6.02/6.26  # Removed by relevancy pruning/SinE    : 0
% 6.02/6.26  # Initial clauses                      : 54
% 6.02/6.26  # Removed in clause preprocessing      : 27
% 6.02/6.26  # Initial clauses in saturation        : 27
% 6.02/6.26  # Processed clauses                    : 22673
% 6.02/6.26  # ...of these trivial                  : 13
% 6.02/6.26  # ...subsumed                          : 14502
% 6.02/6.26  # ...remaining for further processing  : 8158
% 6.02/6.26  # Other redundant clauses eliminated   : 240
% 6.02/6.26  # Clauses deleted for lack of memory   : 0
% 6.02/6.26  # Backward-subsumed                    : 1499
% 6.02/6.26  # Backward-rewritten                   : 4872
% 6.02/6.26  # Generated clauses                    : 216802
% 6.02/6.26  # ...of the previous two non-trivial   : 217565
% 6.02/6.26  # Contextual simplify-reflections      : 910
% 6.02/6.26  # Paramodulations                      : 216357
% 6.02/6.26  # Factorizations                       : 207
% 6.02/6.26  # Equation resolutions                 : 240
% 6.02/6.26  # Propositional unsat checks           : 0
% 6.02/6.26  #    Propositional check models        : 0
% 6.02/6.26  #    Propositional check unsatisfiable : 0
% 6.02/6.26  #    Propositional clauses             : 0
% 6.02/6.26  #    Propositional clauses after purity: 0
% 6.02/6.26  #    Propositional unsat core size     : 0
% 6.02/6.26  #    Propositional preprocessing time  : 0.000
% 6.02/6.26  #    Propositional encoding time       : 0.000
% 6.02/6.26  #    Propositional solver time         : 0.000
% 6.02/6.26  #    Success case prop preproc time    : 0.000
% 6.02/6.26  #    Success case prop encoding time   : 0.000
% 6.02/6.26  #    Success case prop solver time     : 0.000
% 6.02/6.26  # Current number of processed clauses  : 1757
% 6.02/6.26  #    Positive orientable unit clauses  : 15
% 6.02/6.26  #    Positive unorientable unit clauses: 1
% 6.02/6.26  #    Negative unit clauses             : 1
% 6.02/6.26  #    Non-unit-clauses                  : 1740
% 6.02/6.26  # Current number of unprocessed clauses: 189817
% 6.02/6.26  # ...number of literals in the above   : 1430667
% 6.02/6.26  # Current number of archived formulas  : 0
% 6.02/6.26  # Current number of archived clauses   : 6398
% 6.02/6.26  # Clause-clause subsumption calls (NU) : 15275984
% 6.02/6.26  # Rec. Clause-clause subsumption calls : 554918
% 6.02/6.26  # Non-unit clause-clause subsumptions  : 16878
% 6.02/6.26  # Unit Clause-clause subsumption calls : 14958
% 6.02/6.26  # Rewrite failures with RHS unbound    : 0
% 6.02/6.26  # BW rewrite match attempts            : 444
% 6.02/6.26  # BW rewrite match successes           : 177
% 6.02/6.26  # Condensation attempts                : 0
% 6.02/6.26  # Condensation successes               : 0
% 6.02/6.26  # Termbank termtop insertions          : 9509163
% 6.12/6.27  
% 6.12/6.27  # -------------------------------------------------
% 6.12/6.27  # User time                : 5.816 s
% 6.12/6.27  # System time              : 0.112 s
% 6.12/6.27  # Total time               : 5.929 s
% 6.12/6.27  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
