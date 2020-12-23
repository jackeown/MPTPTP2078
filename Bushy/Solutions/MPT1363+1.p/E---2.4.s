%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : compts_1__t18_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:50 EDT 2019

% Result     : Theorem 153.06s
% Output     : CNFRefutation 153.06s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 502 expanded)
%              Number of clauses        :   63 ( 190 expanded)
%              Number of leaves         :   17 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  355 (2704 expanded)
%              Number of equality atoms :   35 ( 115 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',dt_k1_pre_topc)).

fof(t18_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_compts_1(X2,X1)
                  & r1_tarski(X3,X2)
                  & v4_pre_topc(X3,X1) )
               => v2_compts_1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t18_compts_1)).

fof(t11_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X3,k2_struct_0(X2))
               => ( v2_compts_1(X3,X1)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X4 = X3
                       => v2_compts_1(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t11_compts_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',cc1_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',existence_m1_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t3_subset)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',dt_m1_pre_topc)).

fof(t34_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v4_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t34_tops_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t6_boole)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t2_subset)).

fof(cc1_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v2_compts_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',cc1_compts_1)).

fof(t17_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v1_compts_1(X1)
              & v4_pre_topc(X2,X1) )
           => v2_compts_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t17_compts_1)).

fof(t12_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( X2 = k1_xboole_0
             => ( v2_compts_1(X2,X1)
              <=> v1_compts_1(k1_pre_topc(X1,X2)) ) )
            & ( v2_pre_topc(X1)
             => ( X2 = k1_xboole_0
                | ( v2_compts_1(X2,X1)
                <=> v1_compts_1(k1_pre_topc(X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t12_compts_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',dt_o_0_0_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t18_compts_1.p',t5_subset)).

fof(c_0_17,plain,(
    ! [X11,X12,X13] :
      ( ( X13 != k1_pre_topc(X11,X12)
        | k2_struct_0(X13) = X12
        | ~ v1_pre_topc(X13)
        | ~ m1_pre_topc(X13,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( k2_struct_0(X13) != X12
        | X13 = k1_pre_topc(X11,X12)
        | ~ v1_pre_topc(X13)
        | ~ m1_pre_topc(X13,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_18,plain,(
    ! [X16,X17] :
      ( ( v1_pre_topc(k1_pre_topc(X16,X17))
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) )
      & ( m1_pre_topc(k1_pre_topc(X16,X17),X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v2_compts_1(X2,X1)
                    & r1_tarski(X3,X2)
                    & v4_pre_topc(X3,X1) )
                 => v2_compts_1(X3,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_compts_1])).

cnf(c_0_20,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v2_compts_1(esk2_0,esk1_0)
    & r1_tarski(esk3_0,esk2_0)
    & v4_pre_topc(esk3_0,esk1_0)
    & ~ v2_compts_1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_24,plain,(
    ! [X33,X34,X35,X36] :
      ( ( ~ v2_compts_1(X35,X33)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | X36 != X35
        | v2_compts_1(X36,X34)
        | ~ r1_tarski(X35,k2_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk8_3(X33,X34,X35),k1_zfmisc_1(u1_struct_0(X34)))
        | v2_compts_1(X35,X33)
        | ~ r1_tarski(X35,k2_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( esk8_3(X33,X34,X35) = X35
        | v2_compts_1(X35,X33)
        | ~ r1_tarski(X35,k2_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ v2_compts_1(esk8_3(X33,X34,X35),X34)
        | v2_compts_1(X35,X33)
        | ~ r1_tarski(X35,k2_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).

cnf(c_0_25,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( esk8_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk1_0,esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_30,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_compts_1(esk8_3(X1,X2,X3),X2)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( esk8_3(X1,k1_pre_topc(esk1_0,esk2_0),X2) = X2
    | v2_compts_1(X2,X1)
    | ~ m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1)
    | ~ r1_tarski(X2,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v2_compts_1(X1,X2)
    | ~ m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X2)
    | ~ r1_tarski(X1,esk2_0)
    | ~ v2_compts_1(esk8_3(X2,k1_pre_topc(esk1_0,esk2_0),X1),k1_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

fof(c_0_35,plain,(
    ! [X65,X66] :
      ( ~ v1_xboole_0(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(X65))
      | v1_xboole_0(X66) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_36,plain,(
    ! [X27] : m1_subset_1(esk7_1(X27),X27) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_37,plain,(
    ! [X50,X51] :
      ( ( ~ m1_subset_1(X50,k1_zfmisc_1(X51))
        | r1_tarski(X50,X51) )
      & ( ~ r1_tarski(X50,X51)
        | m1_subset_1(X50,k1_zfmisc_1(X51)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_38,negated_conjecture,
    ( v2_compts_1(X1,X2)
    | m1_subset_1(esk8_3(X2,k1_pre_topc(esk1_0,esk2_0),X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0))))
    | ~ m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X2)
    | ~ r1_tarski(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( esk8_3(X1,k1_pre_topc(esk1_0,esk2_0),esk3_0) = esk3_0
    | v2_compts_1(esk3_0,X1)
    | ~ m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_26]),c_0_27])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_43,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | l1_pre_topc(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_44,negated_conjecture,
    ( v2_compts_1(esk3_0,X1)
    | ~ m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1)
    | ~ v2_compts_1(esk8_3(X1,k1_pre_topc(esk1_0,esk2_0),esk3_0),k1_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

fof(c_0_45,plain,(
    ! [X46,X47,X48,X49] :
      ( ~ l1_pre_topc(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | ~ m1_pre_topc(X48,X46)
      | ~ v4_pre_topc(X47,X46)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | X49 != X47
      | v4_pre_topc(X49,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_tops_2])])])).

fof(c_0_46,plain,(
    ! [X58] :
      ( ~ v1_xboole_0(X58)
      | X58 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_49,plain,(
    ! [X52,X53,X54] :
      ( ~ r2_hidden(X52,X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(X54))
      | m1_subset_1(X52,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_51,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X44,X45)
      | v1_xboole_0(X45)
      | r2_hidden(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_52,plain,(
    ! [X63,X64] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | ~ v1_xboole_0(X64)
      | v2_compts_1(X64,X63) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_compts_1])])])).

fof(c_0_53,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
      | ~ v1_compts_1(X40)
      | ~ v4_pre_topc(X41,X40)
      | v2_compts_1(X41,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_compts_1])])])).

cnf(c_0_54,negated_conjecture,
    ( v2_compts_1(esk3_0,X1)
    | m1_subset_1(esk8_3(X1,k1_pre_topc(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0))))
    | ~ m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( esk8_3(esk1_0,k1_pre_topc(esk1_0,esk2_0),esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_27])]),c_0_42])).

cnf(c_0_56,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_compts_1(esk8_3(esk1_0,k1_pre_topc(esk1_0,esk2_0),esk3_0),k1_pre_topc(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_41]),c_0_27])]),c_0_42])).

fof(c_0_58,plain,(
    ! [X38,X39] :
      ( ( ~ v2_compts_1(X39,X38)
        | v1_compts_1(k1_pre_topc(X38,X39))
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( ~ v1_compts_1(k1_pre_topc(X38,X39))
        | v2_compts_1(X39,X38)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( ~ v2_compts_1(X39,X38)
        | v1_compts_1(k1_pre_topc(X38,X39))
        | X39 = k1_xboole_0
        | ~ v2_pre_topc(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( ~ v1_compts_1(k1_pre_topc(X38,X39))
        | v2_compts_1(X39,X38)
        | X39 = k1_xboole_0
        | ~ v2_pre_topc(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_compts_1])])])])).

cnf(c_0_59,plain,
    ( v4_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( v1_xboole_0(esk7_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_62,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_33])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_40]),c_0_55]),c_0_41]),c_0_27])]),c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_40]),c_0_27])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,k1_pre_topc(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_55])).

cnf(c_0_71,plain,
    ( v1_compts_1(k1_pre_topc(X2,X1))
    | X1 = k1_xboole_0
    | ~ v2_compts_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_73,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_74,plain,
    ( v4_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ v4_pre_topc(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_75,plain,
    ( esk7_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_76,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_62])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk7_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_48])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_41]),c_0_27])]),c_0_42])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_compts_1(k1_pre_topc(esk1_0,esk2_0))
    | ~ v4_pre_topc(esk3_0,k1_pre_topc(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])]),c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_26]),c_0_72]),c_0_27]),c_0_73])])).

cnf(c_0_82,negated_conjecture,
    ( v4_pre_topc(esk3_0,k1_pre_topc(esk1_0,esk2_0))
    | ~ m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1)
    | ~ v4_pre_topc(esk3_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_84,plain,(
    ! [X55,X56,X57] :
      ( ~ r2_hidden(X55,X56)
      | ~ m1_subset_1(X56,k1_zfmisc_1(X57))
      | ~ v1_xboole_0(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_85,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_75])).

cnf(c_0_86,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk7_1(esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_64]),c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v4_pre_topc(esk3_0,k1_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( v4_pre_topc(esk3_0,k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_40]),c_0_41]),c_0_27])])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_92,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk7_1(esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_87]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_95,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_86])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_95]),
    [proof]).
%------------------------------------------------------------------------------
