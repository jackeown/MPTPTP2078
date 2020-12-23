%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 595 expanded)
%              Number of clauses        :   90 ( 264 expanded)
%              Number of leaves         :   20 ( 152 expanded)
%              Depth                    :   15
%              Number of atoms          :  327 (1818 expanded)
%              Number of equality atoms :   61 ( 403 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t15_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(t14_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t2_yellow19,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
            & v2_waybel_0(X2,k3_yellow_1(X1))
            & v13_waybel_0(X2,k3_yellow_1(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
         => ! [X3] :
              ~ ( r2_hidden(X3,X2)
                & v1_xboole_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(c_0_20,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X37,X36)
        | r1_tarski(X37,X35)
        | X36 != k1_zfmisc_1(X35) )
      & ( ~ r1_tarski(X38,X35)
        | r2_hidden(X38,X36)
        | X36 != k1_zfmisc_1(X35) )
      & ( ~ r2_hidden(esk5_2(X39,X40),X40)
        | ~ r1_tarski(esk5_2(X39,X40),X39)
        | X40 = k1_zfmisc_1(X39) )
      & ( r2_hidden(esk5_2(X39,X40),X40)
        | r1_tarski(esk5_2(X39,X40),X39)
        | X40 = k1_zfmisc_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
           => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t15_yellow19])).

fof(c_0_22,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X31] : r1_tarski(k1_xboole_0,X31) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_26,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k7_subset_1(X42,X43,X44) = k4_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_27,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k5_xboole_0(X28,k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & ~ v1_xboole_0(esk7_0)
    & v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0))))
    & v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk6_0)))
    & v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk6_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0)))))
    & esk7_0 != k2_yellow19(esk6_0,k3_yellow19(esk6_0,k2_struct_0(esk6_0),esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_29,plain,(
    ! [X50] : k3_yellow_1(X50) = k3_lattice3(k1_lattice3(X50)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_30,plain,(
    ! [X26,X27] :
      ( ( r1_tarski(X26,X27)
        | X26 != X27 )
      & ( r1_tarski(X27,X26)
        | X26 != X27 )
      & ( ~ r1_tarski(X26,X27)
        | ~ r1_tarski(X27,X26)
        | X26 = X27 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r1_xboole_0(X20,X21)
        | r2_hidden(esk4_2(X20,X21),k3_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X25,k3_xboole_0(X23,X24))
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_34,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk3_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk3_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_35,plain,(
    ! [X33,X34] : k2_xboole_0(X33,X34) = k5_xboole_0(X33,k4_xboole_0(X34,X33)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_36,plain,(
    ! [X45,X46] :
      ( ~ r2_hidden(X45,X46)
      | m1_subset_1(k1_tarski(X45),k1_zfmisc_1(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_39,plain,(
    ! [X51,X52] :
      ( v2_struct_0(X51)
      | ~ l1_struct_0(X51)
      | v1_xboole_0(X52)
      | ~ v2_waybel_0(X52,k3_yellow_1(k2_struct_0(X51)))
      | ~ v13_waybel_0(X52,k3_yellow_1(k2_struct_0(X51)))
      | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X51)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X51))),X52,k1_tarski(k1_xboole_0)) = k2_yellow19(X51,k3_yellow19(X51,k2_struct_0(X51),X52)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

cnf(c_0_40,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_49,plain,(
    ! [X30] : k2_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_51,plain,(
    ! [X32] : k4_xboole_0(k1_xboole_0,X32) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_52,plain,(
    ! [X53,X54,X55] :
      ( v1_xboole_0(X53)
      | v1_xboole_0(X54)
      | ~ v1_subset_1(X54,u1_struct_0(k3_yellow_1(X53)))
      | ~ v2_waybel_0(X54,k3_yellow_1(X53))
      | ~ v13_waybel_0(X54,k3_yellow_1(X53))
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X53))))
      | ~ r2_hidden(X55,X54)
      | ~ v1_xboole_0(X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).

fof(c_0_53,plain,(
    ! [X47,X48] :
      ( ( ~ m1_subset_1(X47,k1_zfmisc_1(X48))
        | r1_tarski(X47,X48) )
      & ( ~ r1_tarski(X47,X48)
        | m1_subset_1(X47,k1_zfmisc_1(X48)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_59,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk6_0)))))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_48])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_41])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_70,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_71,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_72,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_lattice3(k1_lattice3(k2_struct_0(esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( v2_waybel_0(esk7_0,k3_lattice3(k1_lattice3(k2_struct_0(esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_74,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_77,negated_conjecture,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk6_0)))),esk7_0,X1) = k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_78,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_79,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_41])).

cnf(c_0_82,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_85,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_86,plain,
    ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,k1_tarski(k1_xboole_0))) = k2_yellow19(esk6_0,k3_yellow19(esk6_0,k2_struct_0(esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74]),c_0_60])]),c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( esk7_0 != k2_yellow19(esk6_0,k3_yellow19(esk6_0,k2_struct_0(esk6_0),esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_91,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_82,c_0_31])).

cnf(c_0_92,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk6_0))))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_43])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_95,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_45])).

cnf(c_0_96,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_97,plain,
    ( r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_32])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_90])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk6_0))
    | ~ r2_hidden(X1,esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_72]),c_0_92]),c_0_73]),c_0_60])])).

cnf(c_0_101,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_102,plain,
    ( r1_xboole_0(X1,k1_zfmisc_1(X2))
    | r1_tarski(esk3_2(X1,k1_zfmisc_1(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_48])).

cnf(c_0_103,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_104,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_93])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(esk2_2(X1,X2))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_106,plain,
    ( esk2_2(k1_zfmisc_1(k1_xboole_0),X1) = k1_xboole_0
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_107,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_108,plain,
    ( r2_hidden(esk1_1(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_47]),c_0_99])).

cnf(c_0_109,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | v1_xboole_0(k2_struct_0(esk6_0))
    | ~ v1_xboole_0(esk3_2(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_110,plain,
    ( esk3_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | r1_xboole_0(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_102])).

cnf(c_0_111,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_112,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)
    | ~ r2_hidden(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107])])).

cnf(c_0_113,plain,
    ( r1_tarski(esk1_1(k1_tarski(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( r1_xboole_0(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k2_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_107])])).

cnf(c_0_115,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_111])).

cnf(c_0_116,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(esk1_1(X1)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_47])).

cnf(c_0_117,plain,
    ( esk1_1(k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_113])).

cnf(c_0_118,negated_conjecture,
    ( v1_xboole_0(k3_xboole_0(esk7_0,k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(k2_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( k2_yellow19(esk6_0,k3_yellow19(esk6_0,k2_struct_0(esk6_0),esk7_0)) = k7_subset_1(esk7_0,esk7_0,k1_tarski(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_115])).

cnf(c_0_120,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_107])]),c_0_99])).

cnf(c_0_121,negated_conjecture,
    ( k3_xboole_0(esk7_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k2_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( k7_subset_1(esk7_0,esk7_0,k1_tarski(k1_xboole_0)) != esk7_0 ),
    inference(rw,[status(thm)],[c_0_90,c_0_119])).

cnf(c_0_123,plain,
    ( k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_120]),c_0_86])])).

fof(c_0_124,plain,(
    ! [X49] :
      ( v2_struct_0(X49)
      | ~ l1_struct_0(X49)
      | ~ v1_xboole_0(k2_struct_0(X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_125,negated_conjecture,
    ( k7_subset_1(esk7_0,esk7_0,k1_zfmisc_1(k1_xboole_0)) = esk7_0
    | v1_xboole_0(k2_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_121]),c_0_89])).

cnf(c_0_126,negated_conjecture,
    ( k7_subset_1(esk7_0,esk7_0,k1_zfmisc_1(k1_xboole_0)) != esk7_0 ),
    inference(rw,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_127,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_128,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_74])]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.19/0.47  # and selection function SelectNewComplexAHPNS.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.029 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.47  fof(t15_yellow19, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 0.19/0.47  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.47  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.47  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.47  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.19/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.47  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.47  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.47  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.47  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.19/0.47  fof(t14_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 0.19/0.47  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.47  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.47  fof(t2_yellow19, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 0.19/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.47  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.47  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.19/0.47  fof(c_0_20, plain, ![X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X37,X36)|r1_tarski(X37,X35)|X36!=k1_zfmisc_1(X35))&(~r1_tarski(X38,X35)|r2_hidden(X38,X36)|X36!=k1_zfmisc_1(X35)))&((~r2_hidden(esk5_2(X39,X40),X40)|~r1_tarski(esk5_2(X39,X40),X39)|X40=k1_zfmisc_1(X39))&(r2_hidden(esk5_2(X39,X40),X40)|r1_tarski(esk5_2(X39,X40),X39)|X40=k1_zfmisc_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.47  fof(c_0_21, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))))), inference(assume_negation,[status(cth)],[t15_yellow19])).
% 0.19/0.47  fof(c_0_22, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.47  fof(c_0_23, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.47  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  fof(c_0_25, plain, ![X31]:r1_tarski(k1_xboole_0,X31), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.47  fof(c_0_26, plain, ![X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|k7_subset_1(X42,X43,X44)=k4_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.47  fof(c_0_27, plain, ![X28, X29]:k4_xboole_0(X28,X29)=k5_xboole_0(X28,k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.47  fof(c_0_28, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_struct_0(esk6_0))&(((((~v1_xboole_0(esk7_0)&v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0)))))&v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk6_0))))&v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk6_0))))&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0))))))&esk7_0!=k2_yellow19(esk6_0,k3_yellow19(esk6_0,k2_struct_0(esk6_0),esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.19/0.47  fof(c_0_29, plain, ![X50]:k3_yellow_1(X50)=k3_lattice3(k1_lattice3(X50)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.19/0.47  fof(c_0_30, plain, ![X26, X27]:(((r1_tarski(X26,X27)|X26!=X27)&(r1_tarski(X27,X26)|X26!=X27))&(~r1_tarski(X26,X27)|~r1_tarski(X27,X26)|X26=X27)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.47  cnf(c_0_31, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_32, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  fof(c_0_33, plain, ![X20, X21, X23, X24, X25]:((r1_xboole_0(X20,X21)|r2_hidden(esk4_2(X20,X21),k3_xboole_0(X20,X21)))&(~r2_hidden(X25,k3_xboole_0(X23,X24))|~r1_xboole_0(X23,X24))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.47  fof(c_0_34, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk3_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk3_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.47  fof(c_0_35, plain, ![X33, X34]:k2_xboole_0(X33,X34)=k5_xboole_0(X33,k4_xboole_0(X34,X33)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.47  fof(c_0_36, plain, ![X45, X46]:(~r2_hidden(X45,X46)|m1_subset_1(k1_tarski(X45),k1_zfmisc_1(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.19/0.47  cnf(c_0_37, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  fof(c_0_39, plain, ![X51, X52]:(v2_struct_0(X51)|~l1_struct_0(X51)|(v1_xboole_0(X52)|~v2_waybel_0(X52,k3_yellow_1(k2_struct_0(X51)))|~v13_waybel_0(X52,k3_yellow_1(k2_struct_0(X51)))|~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X51)))))|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X51))),X52,k1_tarski(k1_xboole_0))=k2_yellow19(X51,k3_yellow19(X51,k2_struct_0(X51),X52)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).
% 0.19/0.47  cnf(c_0_40, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.47  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0)))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.47  cnf(c_0_43, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.47  cnf(c_0_44, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.47  cnf(c_0_46, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.47  cnf(c_0_47, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_48, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  fof(c_0_49, plain, ![X30]:k2_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.47  cnf(c_0_50, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  fof(c_0_51, plain, ![X32]:k4_xboole_0(k1_xboole_0,X32)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.47  fof(c_0_52, plain, ![X53, X54, X55]:(v1_xboole_0(X53)|(v1_xboole_0(X54)|~v1_subset_1(X54,u1_struct_0(k3_yellow_1(X53)))|~v2_waybel_0(X54,k3_yellow_1(X53))|~v13_waybel_0(X54,k3_yellow_1(X53))|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X53))))|(~r2_hidden(X55,X54)|~v1_xboole_0(X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).
% 0.19/0.47  fof(c_0_53, plain, ![X47, X48]:((~m1_subset_1(X47,k1_zfmisc_1(X48))|r1_tarski(X47,X48))&(~r1_tarski(X47,X48)|m1_subset_1(X47,k1_zfmisc_1(X48)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.47  cnf(c_0_54, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_55, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.47  cnf(c_0_56, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.47  cnf(c_0_58, negated_conjecture, (v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.47  cnf(c_0_59, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk6_0))))))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.47  cnf(c_0_61, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.47  cnf(c_0_62, plain, (v1_xboole_0(k3_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.47  cnf(c_0_63, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_31, c_0_48])).
% 0.19/0.47  cnf(c_0_64, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.47  cnf(c_0_65, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_50, c_0_41])).
% 0.19/0.47  cnf(c_0_66, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.47  cnf(c_0_67, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))|~v2_waybel_0(X2,k3_yellow_1(X1))|~v13_waybel_0(X2,k3_yellow_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.47  cnf(c_0_68, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.47  cnf(c_0_70, plain, (m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.47  cnf(c_0_71, plain, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (v13_waybel_0(esk7_0,k3_lattice3(k1_lattice3(k2_struct_0(esk6_0))))), inference(rw,[status(thm)],[c_0_57, c_0_43])).
% 0.19/0.47  cnf(c_0_73, negated_conjecture, (v2_waybel_0(esk7_0,k3_lattice3(k1_lattice3(k2_struct_0(esk6_0))))), inference(rw,[status(thm)],[c_0_58, c_0_43])).
% 0.19/0.47  cnf(c_0_74, negated_conjecture, (l1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.47  cnf(c_0_75, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.47  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.47  cnf(c_0_77, negated_conjecture, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk6_0)))),esk7_0,X1)=k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.47  cnf(c_0_78, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_38])).
% 0.19/0.47  cnf(c_0_79, plain, (v1_xboole_0(k3_xboole_0(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.47  cnf(c_0_80, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.47  cnf(c_0_81, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_66, c_0_41])).
% 0.19/0.47  cnf(c_0_82, plain, (v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_xboole_0(X3)|~r2_hidden(X3,X2)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.19/0.47  cnf(c_0_83, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.47  cnf(c_0_84, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_68])).
% 0.19/0.47  cnf(c_0_85, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_86, plain, (r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.47  cnf(c_0_87, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,k1_tarski(k1_xboole_0)))=k2_yellow19(esk6_0,k3_yellow19(esk6_0,k2_struct_0(esk6_0),esk7_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74]), c_0_60])]), c_0_75]), c_0_76]), c_0_77])).
% 0.19/0.47  cnf(c_0_88, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.47  cnf(c_0_89, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.47  cnf(c_0_90, negated_conjecture, (esk7_0!=k2_yellow19(esk6_0,k3_yellow19(esk6_0,k2_struct_0(esk6_0),esk7_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.47  cnf(c_0_91, plain, (v1_xboole_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_82, c_0_31])).
% 0.19/0.47  cnf(c_0_92, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk6_0)))))), inference(rw,[status(thm)],[c_0_83, c_0_43])).
% 0.19/0.47  cnf(c_0_93, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_94, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_95, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_45])).
% 0.19/0.47  cnf(c_0_96, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 0.19/0.47  cnf(c_0_97, plain, (r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_84, c_0_32])).
% 0.19/0.47  cnf(c_0_98, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.47  cnf(c_0_99, negated_conjecture, (~v1_xboole_0(k1_tarski(k1_xboole_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_90])).
% 0.19/0.47  cnf(c_0_100, negated_conjecture, (v1_xboole_0(k2_struct_0(esk6_0))|~r2_hidden(X1,esk7_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_72]), c_0_92]), c_0_73]), c_0_60])])).
% 0.19/0.47  cnf(c_0_101, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  cnf(c_0_102, plain, (r1_xboole_0(X1,k1_zfmisc_1(X2))|r1_tarski(esk3_2(X1,k1_zfmisc_1(X2)),X2)), inference(spm,[status(thm)],[c_0_84, c_0_48])).
% 0.19/0.47  cnf(c_0_103, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.47  cnf(c_0_104, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_93])).
% 0.19/0.47  cnf(c_0_105, plain, (r1_tarski(X1,X2)|~r2_hidden(X3,X2)|~v1_xboole_0(esk2_2(X1,X2))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.47  cnf(c_0_106, plain, (esk2_2(k1_zfmisc_1(k1_xboole_0),X1)=k1_xboole_0|r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.47  cnf(c_0_107, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.47  cnf(c_0_108, plain, (r2_hidden(esk1_1(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_47]), c_0_99])).
% 0.19/0.47  cnf(c_0_109, negated_conjecture, (r1_xboole_0(esk7_0,X1)|v1_xboole_0(k2_struct_0(esk6_0))|~v1_xboole_0(esk3_2(esk7_0,X1))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.47  cnf(c_0_110, plain, (esk3_2(X1,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|r1_xboole_0(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_96, c_0_102])).
% 0.19/0.47  cnf(c_0_111, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.19/0.47  cnf(c_0_112, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)|~r2_hidden(X2,X1)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107])])).
% 0.19/0.47  cnf(c_0_113, plain, (r1_tarski(esk1_1(k1_tarski(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_84, c_0_108])).
% 0.19/0.47  cnf(c_0_114, negated_conjecture, (r1_xboole_0(esk7_0,k1_zfmisc_1(k1_xboole_0))|v1_xboole_0(k2_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_107])])).
% 0.19/0.47  cnf(c_0_115, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_59, c_0_111])).
% 0.19/0.47  cnf(c_0_116, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)|v1_xboole_0(X1)|~v1_xboole_0(esk1_1(X1))), inference(spm,[status(thm)],[c_0_112, c_0_47])).
% 0.19/0.47  cnf(c_0_117, plain, (esk1_1(k1_tarski(k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_113])).
% 0.19/0.47  cnf(c_0_118, negated_conjecture, (v1_xboole_0(k3_xboole_0(esk7_0,k1_zfmisc_1(k1_xboole_0)))|v1_xboole_0(k2_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_62, c_0_114])).
% 0.19/0.47  cnf(c_0_119, negated_conjecture, (k2_yellow19(esk6_0,k3_yellow19(esk6_0,k2_struct_0(esk6_0),esk7_0))=k7_subset_1(esk7_0,esk7_0,k1_tarski(k1_xboole_0))), inference(rw,[status(thm)],[c_0_87, c_0_115])).
% 0.19/0.47  cnf(c_0_120, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_107])]), c_0_99])).
% 0.19/0.47  cnf(c_0_121, negated_conjecture, (k3_xboole_0(esk7_0,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|v1_xboole_0(k2_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_78, c_0_118])).
% 0.19/0.47  cnf(c_0_122, negated_conjecture, (k7_subset_1(esk7_0,esk7_0,k1_tarski(k1_xboole_0))!=esk7_0), inference(rw,[status(thm)],[c_0_90, c_0_119])).
% 0.19/0.47  cnf(c_0_123, plain, (k1_tarski(k1_xboole_0)=k1_zfmisc_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_120]), c_0_86])])).
% 0.19/0.47  fof(c_0_124, plain, ![X49]:(v2_struct_0(X49)|~l1_struct_0(X49)|~v1_xboole_0(k2_struct_0(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.19/0.47  cnf(c_0_125, negated_conjecture, (k7_subset_1(esk7_0,esk7_0,k1_zfmisc_1(k1_xboole_0))=esk7_0|v1_xboole_0(k2_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_121]), c_0_89])).
% 0.19/0.47  cnf(c_0_126, negated_conjecture, (k7_subset_1(esk7_0,esk7_0,k1_zfmisc_1(k1_xboole_0))!=esk7_0), inference(rw,[status(thm)],[c_0_122, c_0_123])).
% 0.19/0.47  cnf(c_0_127, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.19/0.47  cnf(c_0_128, negated_conjecture, (v1_xboole_0(k2_struct_0(esk6_0))), inference(sr,[status(thm)],[c_0_125, c_0_126])).
% 0.19/0.47  cnf(c_0_129, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_74])]), c_0_75]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 130
% 0.19/0.47  # Proof object clause steps            : 90
% 0.19/0.47  # Proof object formula steps           : 40
% 0.19/0.47  # Proof object conjectures             : 29
% 0.19/0.47  # Proof object clause conjectures      : 26
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 34
% 0.19/0.47  # Proof object initial formulas used   : 20
% 0.19/0.47  # Proof object generating inferences   : 37
% 0.19/0.47  # Proof object simplifying inferences  : 52
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 20
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 39
% 0.19/0.47  # Removed in clause preprocessing      : 3
% 0.19/0.47  # Initial clauses in saturation        : 36
% 0.19/0.47  # Processed clauses                    : 1427
% 0.19/0.47  # ...of these trivial                  : 27
% 0.19/0.47  # ...subsumed                          : 1027
% 0.19/0.47  # ...remaining for further processing  : 373
% 0.19/0.47  # Other redundant clauses eliminated   : 10
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 7
% 0.19/0.47  # Backward-rewritten                   : 54
% 0.19/0.47  # Generated clauses                    : 5155
% 0.19/0.47  # ...of the previous two non-trivial   : 4531
% 0.19/0.47  # Contextual simplify-reflections      : 9
% 0.19/0.47  # Paramodulations                      : 5140
% 0.19/0.47  # Factorizations                       : 4
% 0.19/0.47  # Equation resolutions                 : 10
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 272
% 0.19/0.47  #    Positive orientable unit clauses  : 45
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 6
% 0.19/0.47  #    Non-unit-clauses                  : 221
% 0.19/0.47  # Current number of unprocessed clauses: 3034
% 0.19/0.47  # ...number of literals in the above   : 11763
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 100
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 27266
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 13512
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 749
% 0.19/0.47  # Unit Clause-clause subsumption calls : 436
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 40
% 0.19/0.47  # BW rewrite match successes           : 17
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 55283
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.122 s
% 0.19/0.47  # System time              : 0.009 s
% 0.19/0.47  # Total time               : 0.132 s
% 0.19/0.47  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
