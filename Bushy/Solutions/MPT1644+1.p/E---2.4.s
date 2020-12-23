%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t24_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:46 EDT 2019

% Result     : Theorem 1.20s
% Output     : CNFRefutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 461 expanded)
%              Number of clauses        :   66 ( 187 expanded)
%              Number of leaves         :   11 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          :  362 (2264 expanded)
%              Number of equality atoms :   13 (  66 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',t24_waybel_0)).

fof(d20_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X3,X4) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',d20_waybel_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',d3_tarski)).

fof(d16_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k4_waybel_0(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                          & r1_orders_2(X1,X5,X4)
                          & r2_hidden(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',d16_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',t4_subset)).

fof(dt_k4_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',dt_k4_waybel_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',t7_boole)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',existence_m1_subset_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t24_waybel_0.p',cc1_subset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v13_waybel_0(X2,X1)
            <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_waybel_0])).

fof(c_0_12,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X37,u1_struct_0(X34))
        | ~ r2_hidden(X36,X35)
        | ~ r1_orders_2(X34,X36,X37)
        | r2_hidden(X37,X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( m1_subset_1(esk6_2(X34,X35),u1_struct_0(X34))
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( m1_subset_1(esk7_2(X34,X35),u1_struct_0(X34))
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( r2_hidden(esk6_2(X34,X35),X35)
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( r1_orders_2(X34,esk6_2(X34,X35),esk7_2(X34,X35))
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( ~ r2_hidden(esk7_2(X34,X35),X35)
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v13_waybel_0(esk2_0,esk1_0)
      | ~ r1_tarski(k4_waybel_0(esk1_0,esk2_0),esk2_0) )
    & ( v13_waybel_0(esk2_0,esk1_0)
      | r1_tarski(k4_waybel_0(esk1_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( ( ~ r1_tarski(X40,X41)
        | ~ r2_hidden(X42,X40)
        | r2_hidden(X42,X41) )
      & ( r2_hidden(esk8_2(X43,X44),X43)
        | r1_tarski(X43,X44) )
      & ( ~ r2_hidden(esk8_2(X43,X44),X44)
        | r1_tarski(X43,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X25,X26,X27,X28,X30,X32] :
      ( ( m1_subset_1(esk3_4(X25,X26,X27,X28),u1_struct_0(X25))
        | ~ r2_hidden(X28,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | X27 != k4_waybel_0(X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r1_orders_2(X25,esk3_4(X25,X26,X27,X28),X28)
        | ~ r2_hidden(X28,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | X27 != k4_waybel_0(X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r2_hidden(esk3_4(X25,X26,X27,X28),X26)
        | ~ r2_hidden(X28,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | X27 != k4_waybel_0(X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X25))
        | ~ r1_orders_2(X25,X30,X28)
        | ~ r2_hidden(X30,X26)
        | r2_hidden(X28,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | X27 != k4_waybel_0(X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk4_3(X25,X26,X27),u1_struct_0(X25))
        | X27 = k4_waybel_0(X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( ~ r2_hidden(esk4_3(X25,X26,X27),X27)
        | ~ m1_subset_1(X32,u1_struct_0(X25))
        | ~ r1_orders_2(X25,X32,esk4_3(X25,X26,X27))
        | ~ r2_hidden(X32,X26)
        | X27 = k4_waybel_0(X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk5_3(X25,X26,X27),u1_struct_0(X25))
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k4_waybel_0(X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r1_orders_2(X25,esk5_3(X25,X26,X27),esk4_3(X25,X26,X27))
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k4_waybel_0(X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X26)
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k4_waybel_0(X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_waybel_0])])])])])).

fof(c_0_19,plain,(
    ! [X78,X79,X80] :
      ( ~ r2_hidden(X78,X79)
      | ~ m1_subset_1(X79,k1_zfmisc_1(X80))
      | m1_subset_1(X78,X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_20,plain,(
    ! [X46,X47] :
      ( ~ l1_orders_2(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | m1_subset_1(k4_waybel_0(X46,X47),k1_zfmisc_1(u1_struct_0(X46))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_waybel_0])])).

fof(c_0_21,plain,(
    ! [X85,X86] :
      ( ~ r2_hidden(X85,X86)
      | ~ v1_xboole_0(X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk6_2(esk1_0,esk2_0),esk2_0)
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_24,plain,(
    ! [X76,X77] :
      ( ( ~ m1_subset_1(X76,k1_zfmisc_1(X77))
        | r1_tarski(X76,X77) )
      & ( ~ r1_tarski(X76,X77)
        | m1_subset_1(X76,k1_zfmisc_1(X77)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X5 != k4_waybel_0(X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_2(esk1_0,esk2_0),X1)
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k4_waybel_0(X2,X3))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_25,c_0_26])]),c_0_27])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k4_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_37,plain,(
    ! [X74,X75] :
      ( ~ m1_subset_1(X74,X75)
      | v1_xboole_0(X75)
      | r2_hidden(X74,X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_38,plain,(
    ! [X51] : m1_subset_1(esk11_1(X51),X51) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_2(esk1_0,esk2_0),X1)
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | r1_tarski(k4_waybel_0(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k4_waybel_0(esk1_0,esk2_0))
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_16]),c_0_17])])).

cnf(c_0_43,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | m1_subset_1(esk7_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_17])])).

cnf(c_0_44,plain,
    ( r1_orders_2(X1,esk6_2(X1,X2),esk7_2(X1,X2))
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,plain,
    ( r2_hidden(esk3_4(X1,X2,k4_waybel_0(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k4_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_34,c_0_26])]),c_0_27])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( m1_subset_1(esk11_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,k4_waybel_0(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ r1_tarski(k4_waybel_0(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk6_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | m1_subset_1(k4_waybel_0(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk7_2(esk1_0,esk2_0),k4_waybel_0(esk1_0,esk2_0))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk7_2(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_2(esk1_0,esk2_0),esk7_2(esk1_0,esk2_0))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_17])])).

cnf(c_0_56,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k4_waybel_0(X3,X1))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_45]),c_0_46])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk11_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( r1_tarski(k4_waybel_0(X1,X2),X3)
    | m1_subset_1(esk8_2(k4_waybel_0(X1,X2),X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(k4_waybel_0(esk1_0,esk2_0))
    | ~ v13_waybel_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_60,plain,
    ( v1_xboole_0(k4_waybel_0(X1,X2))
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_52])).

cnf(c_0_62,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_63,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,k4_waybel_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk7_2(esk1_0,esk2_0),k4_waybel_0(esk1_0,esk2_0))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_23])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k4_waybel_0(X1,X2))
    | ~ v1_xboole_0(X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k4_waybel_0(esk1_0,esk2_0),X1)
    | m1_subset_1(esk8_2(k4_waybel_0(esk1_0,esk2_0),X1),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_16]),c_0_17])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_16]),c_0_17])]),c_0_61])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ r2_hidden(X4,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_62,c_0_26])).

cnf(c_0_70,plain,
    ( r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k4_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | m1_subset_1(esk7_2(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_65]),c_0_17])]),c_0_66])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk8_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk8_2(k4_waybel_0(esk1_0,esk2_0),X1),u1_struct_0(esk1_0))
    | r1_tarski(k4_waybel_0(esk1_0,esk2_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_67]),c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_16]),c_0_17])])).

cnf(c_0_76,plain,
    ( r1_orders_2(X1,esk3_4(X1,X2,k4_waybel_0(X1,X2),X3),X3)
    | ~ r2_hidden(X3,k4_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_70,c_0_26])]),c_0_27])).

cnf(c_0_77,plain,
    ( v13_waybel_0(X2,X1)
    | ~ r2_hidden(esk7_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk7_2(esk1_0,esk2_0),esk2_0)
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_71]),c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k4_waybel_0(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(esk3_4(esk1_0,X2,k4_waybel_0(esk1_0,X2),X1),esk2_0)
    | ~ r2_hidden(X1,k4_waybel_0(esk1_0,X2))
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_17])])).

cnf(c_0_81,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_16]),c_0_17])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k4_waybel_0(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(esk3_4(esk1_0,X2,k4_waybel_0(esk1_0,X2),X1),esk2_0)
    | ~ r2_hidden(X1,k4_waybel_0(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,k4_waybel_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k4_waybel_0(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_45]),c_0_16]),c_0_17])]),c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk8_2(k4_waybel_0(esk1_0,esk2_0),X1),esk2_0)
    | r1_tarski(k4_waybel_0(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_29])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_81])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_86]),c_0_87]),
    [proof]).
%------------------------------------------------------------------------------
