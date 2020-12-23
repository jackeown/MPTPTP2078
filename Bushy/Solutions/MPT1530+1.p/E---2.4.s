%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t8_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:48 EDT 2019

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   84 (8454 expanded)
%              Number of clauses        :   73 (3374 expanded)
%              Number of leaves         :    5 (1939 expanded)
%              Depth                    :   23
%              Number of atoms          :  498 (284970 expanded)
%              Number of equality atoms :   38 (6280 expanded)
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t8_yellow_0.p',t8_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t8_yellow_0.p',d9_lattice3)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t8_yellow_0.p',d2_tarski)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t8_yellow_0.p',d8_lattice3)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t8_yellow_0.p',commutativity_k2_tarski)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r2_hidden(X30,X28)
        | r1_orders_2(X27,X30,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk7_3(X27,X28,X29),u1_struct_0(X27))
        | r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( r2_hidden(esk7_3(X27,X28,X29),X28)
        | r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,esk7_3(X27,X28,X29),X29)
        | r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_7,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk4_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X13
        | X16 = X14
        | X15 != k2_tarski(X13,X14) )
      & ( X17 != X13
        | r2_hidden(X17,X15)
        | X15 != k2_tarski(X13,X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k2_tarski(X13,X14) )
      & ( esk5_3(X18,X19,X20) != X18
        | ~ r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k2_tarski(X18,X19) )
      & ( esk5_3(X18,X19,X20) != X19
        | ~ r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k2_tarski(X18,X19) )
      & ( r2_hidden(esk5_3(X18,X19,X20),X20)
        | esk5_3(X18,X19,X20) = X18
        | esk5_3(X18,X19,X20) = X19
        | X20 = k2_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X23)
        | r1_orders_2(X22,X24,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk6_3(X22,X23,X24),u1_struct_0(X22))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk6_3(X22,X23,X24),X23)
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X24,esk6_3(X22,X23,X24))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_10,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,X1)
    | ~ r2_hidden(esk4_0,X2)
    | ~ r2_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,X1,esk2_0),X1)
    | r2_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_12])])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | ~ r2_hidden(esk4_0,X2)
    | ~ r1_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_11]),c_0_12])])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ r2_lattice3(esk1_0,X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk2_0)
    | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk4_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,X1)
    | ~ r2_hidden(esk3_0,X2)
    | ~ r2_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_19]),c_0_12])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( esk7_3(esk1_0,k2_tarski(X1,X2),esk2_0) = X2
    | esk7_3(esk1_0,k2_tarski(X1,X2),esk2_0) = X1
    | r2_lattice3(esk1_0,k2_tarski(X1,X2),esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk4_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ r1_lattice3(esk1_0,X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk4_0)
    | r1_orders_2(esk1_0,esk4_0,esk2_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ r2_lattice3(esk1_0,X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk4_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).

cnf(c_0_35,negated_conjecture,
    ( esk7_3(esk1_0,k2_tarski(X1,X2),esk2_0) = X2
    | r2_lattice3(esk1_0,k2_tarski(X1,X2),esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_15]),c_0_12])])).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25])])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk4_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_38,negated_conjecture,
    ( esk7_3(esk1_0,k2_tarski(esk4_0,X1),esk2_0) = X1
    | r2_lattice3(esk1_0,k2_tarski(esk4_0,X1),esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_39,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_tarski(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_40,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk4_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_37]),c_0_25])])).

cnf(c_0_43,negated_conjecture,
    ( r2_lattice3(esk1_0,k2_tarski(esk4_0,X1),esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk4_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_15]),c_0_12])])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk2_0),X1)
    | r1_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_15]),c_0_12])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk4_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_44])).

cnf(c_0_48,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk6_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( esk6_3(esk1_0,k2_tarski(X1,X2),esk2_0) = X2
    | esk6_3(esk1_0,k2_tarski(X1,X2),esk2_0) = X1
    | r1_lattice3(esk1_0,k2_tarski(X1,X2),esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk4_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk3_0,X2)
    | ~ r1_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_19]),c_0_12])])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk2_0)
    | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_53,negated_conjecture,
    ( esk6_3(esk1_0,k2_tarski(X1,X2),esk2_0) = X2
    | r1_lattice3(esk1_0,k2_tarski(X1,X2),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_15]),c_0_12])])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_50]),c_0_25])])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_lattice3(esk1_0,X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk4_0,esk2_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_52]),c_0_25])])).

cnf(c_0_57,negated_conjecture,
    ( esk6_3(esk1_0,k2_tarski(esk4_0,X1),esk2_0) = X1
    | r1_lattice3(esk1_0,k2_tarski(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk2_0)
    | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_34])])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattice3(esk1_0,k2_tarski(esk4_0,X1),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_57]),c_0_15]),c_0_12])])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_58]),c_0_34])])).

cnf(c_0_63,negated_conjecture,
    ( r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_54])]),c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattice3(esk1_0,k2_tarski(X1,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_44])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_62]),c_0_34])])).

cnf(c_0_67,negated_conjecture,
    ( r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | r1_orders_2(esk1_0,esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_69,negated_conjecture,
    ( r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_54])]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_67]),c_0_25])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_54])])).

cnf(c_0_72,negated_conjecture,
    ( r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_64]),c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( esk7_3(esk1_0,k2_tarski(esk4_0,X1),esk2_0) = X1
    | r2_lattice3(esk1_0,k2_tarski(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_70])]),c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_72]),c_0_34])])).

cnf(c_0_76,negated_conjecture,
    ( r2_lattice3(esk1_0,k2_tarski(esk4_0,X1),esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_73]),c_0_15]),c_0_12])])).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_79,negated_conjecture,
    ( r2_lattice3(esk1_0,k2_tarski(X1,esk4_0),esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_44])).

cnf(c_0_80,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0)
    | ~ r2_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_66]),c_0_60])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_75])])).

cnf(c_0_82,negated_conjecture,
    ( r1_lattice3(esk1_0,k2_tarski(esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_79]),c_0_75])]),c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_82]),c_0_34])]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
