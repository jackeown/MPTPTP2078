%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t16_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:49 EDT 2019

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 385 expanded)
%              Number of clauses        :   40 ( 122 expanded)
%              Number of leaves         :   10 (  97 expanded)
%              Depth                    :   17
%              Number of atoms          :  267 (2988 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   27 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_hidden(X3,k2_yellow19(X1,X2))
            <=> ( r1_waybel_0(X1,X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',t11_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',t14_yellow19)).

fof(t16_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
             => ( r2_hidden(X3,X2)
              <=> r1_waybel_0(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',t16_yellow19)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',redefinition_k7_subset_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',t64_zfmisc_1)).

fof(dt_k3_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & ~ v1_xboole_0(X3)
        & v2_waybel_0(X3,k3_yellow_1(X2))
        & v13_waybel_0(X3,k3_yellow_1(X2))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) )
     => ( ~ v2_struct_0(k3_yellow19(X1,X2,X3))
        & v6_waybel_0(k3_yellow19(X1,X2,X3),X1)
        & l1_waybel_0(k3_yellow19(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',dt_k3_yellow19)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',fc5_struct_0)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',dt_k2_struct_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/yellow19__t16_yellow19.p',d2_xboole_0)).

fof(c_0_10,plain,(
    ! [X65,X66,X67] :
      ( ( r1_waybel_0(X65,X66,X67)
        | ~ r2_hidden(X67,k2_yellow19(X65,X66))
        | v2_struct_0(X66)
        | ~ l1_waybel_0(X66,X65)
        | v2_struct_0(X65)
        | ~ l1_struct_0(X65) )
      & ( m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X65)))
        | ~ r2_hidden(X67,k2_yellow19(X65,X66))
        | v2_struct_0(X66)
        | ~ l1_waybel_0(X66,X65)
        | v2_struct_0(X65)
        | ~ l1_struct_0(X65) )
      & ( ~ r1_waybel_0(X65,X66,X67)
        | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X65)))
        | r2_hidden(X67,k2_yellow19(X65,X66))
        | v2_struct_0(X66)
        | ~ l1_waybel_0(X66,X65)
        | v2_struct_0(X65)
        | ~ l1_struct_0(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t11_yellow19])])])])])).

fof(c_0_11,plain,(
    ! [X68,X69] :
      ( v2_struct_0(X68)
      | ~ l1_struct_0(X68)
      | v1_xboole_0(X69)
      | ~ v2_waybel_0(X69,k3_yellow_1(k2_struct_0(X68)))
      | ~ v13_waybel_0(X69,k3_yellow_1(k2_struct_0(X68)))
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X68)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X68))),X69,k1_tarski(k1_xboole_0)) = k2_yellow19(X68,k3_yellow19(X68,k2_struct_0(X68),X69)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
               => ( r2_hidden(X3,X2)
                <=> r1_waybel_0(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_yellow19])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,k2_yellow19(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))
    & ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ r2_hidden(esk3_0,esk2_0)
      | ~ r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) )
    & ( r2_hidden(esk3_0,esk2_0)
      | r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2))),X3,k1_tarski(k1_xboole_0)))
    | v1_xboole_0(X3)
    | v2_struct_0(k3_yellow19(X2,k2_struct_0(X2),X3))
    | v2_struct_0(X2)
    | ~ l1_waybel_0(k3_yellow19(X2,k2_struct_0(X2),X3),X2)
    | ~ r1_waybel_0(X2,k3_yellow19(X2,k2_struct_0(X2),X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X2)))
    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X2)))
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X62,X63,X64] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(X62))
      | k7_subset_1(X62,X63,X64) = k4_xboole_0(X63,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_26,plain,(
    ! [X87,X88,X89] :
      ( ( r2_hidden(X87,X88)
        | ~ r2_hidden(X87,k4_xboole_0(X88,k1_tarski(X89))) )
      & ( X87 != X89
        | ~ r2_hidden(X87,k4_xboole_0(X88,k1_tarski(X89))) )
      & ( ~ r2_hidden(X87,X88)
        | X87 = X89
        | r2_hidden(X87,k4_xboole_0(X88,k1_tarski(X89))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))),esk2_0,k1_tarski(k1_xboole_0)))
    | r2_hidden(esk3_0,esk2_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_28,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v2_struct_0(k3_yellow19(X26,X27,X28))
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v1_xboole_0(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | v1_xboole_0(X28)
        | ~ v2_waybel_0(X28,k3_yellow_1(X27))
        | ~ v13_waybel_0(X28,k3_yellow_1(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X27)))) )
      & ( v6_waybel_0(k3_yellow19(X26,X27,X28),X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v1_xboole_0(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | v1_xboole_0(X28)
        | ~ v2_waybel_0(X28,k3_yellow_1(X27))
        | ~ v13_waybel_0(X28,k3_yellow_1(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X27)))) )
      & ( l1_waybel_0(k3_yellow19(X26,X27,X28),X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v1_xboole_0(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | v1_xboole_0(X28)
        | ~ v2_waybel_0(X28,k3_yellow_1(X27))
        | ~ v13_waybel_0(X28,k3_yellow_1(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X27)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_18])]),c_0_29])).

cnf(c_0_32,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_33,plain,(
    ! [X95] :
      ( v2_struct_0(X95)
      | ~ l1_struct_0(X95)
      | ~ v1_xboole_0(k2_struct_0(X95)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_18]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

fof(c_0_38,plain,(
    ! [X23] :
      ( ~ l1_struct_0(X23)
      | m1_subset_1(k2_struct_0(X23),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_22])]),c_0_24])).

cnf(c_0_40,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_41,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0)
    | ~ r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_22])])).

cnf(c_0_44,plain,
    ( r1_waybel_0(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
    | v1_xboole_0(X2)
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2),X1)
    | ~ r2_hidden(X3,k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_46,plain,
    ( r1_waybel_0(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
    | v1_xboole_0(X2)
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2),X1)
    | ~ r2_hidden(X3,k4_xboole_0(X2,k1_tarski(k1_xboole_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ r2_hidden(esk3_0,k4_xboole_0(esk2_0,k1_tarski(k1_xboole_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_18]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_48,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_43])])).

cnf(c_0_50,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_32]),c_0_18]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_50]),c_0_18]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_52,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_51]),c_0_22])]),c_0_24])).

cnf(c_0_53,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_54,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_40]),c_0_22])])).

cnf(c_0_57,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
