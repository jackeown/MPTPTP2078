%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1381+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 26.71s
% Output     : CNFRefutation 26.71s
% Verified   : 
% Statistics : Number of formulae       :   27 (  49 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  107 ( 255 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( m1_connsp_2(X2,X1,X3)
               => r2_hidden(X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT019+2.ax',t44_tops_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( m1_connsp_2(X2,X1,X3)
                 => r2_hidden(X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_connsp_2])).

fof(c_0_6,plain,(
    ! [X6900,X6901] :
      ( ~ l1_pre_topc(X6900)
      | ~ m1_subset_1(X6901,k1_zfmisc_1(u1_struct_0(X6900)))
      | r1_tarski(k1_tops_1(X6900,X6901),X6901) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk809_0)
    & v2_pre_topc(esk809_0)
    & l1_pre_topc(esk809_0)
    & m1_subset_1(esk810_0,k1_zfmisc_1(u1_struct_0(esk809_0)))
    & m1_subset_1(esk811_0,u1_struct_0(esk809_0))
    & m1_connsp_2(esk810_0,esk809_0,esk811_0)
    & ~ r2_hidden(esk811_0,esk810_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X7764,X7765,X7766] :
      ( ( ~ m1_connsp_2(X7766,X7764,X7765)
        | r2_hidden(X7765,k1_tops_1(X7764,X7766))
        | ~ m1_subset_1(X7766,k1_zfmisc_1(u1_struct_0(X7764)))
        | ~ m1_subset_1(X7765,u1_struct_0(X7764))
        | v2_struct_0(X7764)
        | ~ v2_pre_topc(X7764)
        | ~ l1_pre_topc(X7764) )
      & ( ~ r2_hidden(X7765,k1_tops_1(X7764,X7766))
        | m1_connsp_2(X7766,X7764,X7765)
        | ~ m1_subset_1(X7766,k1_zfmisc_1(u1_struct_0(X7764)))
        | ~ m1_subset_1(X7765,u1_struct_0(X7764))
        | v2_struct_0(X7764)
        | ~ v2_pre_topc(X7764)
        | ~ l1_pre_topc(X7764) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_9,plain,(
    ! [X7767,X7768,X7769] :
      ( v2_struct_0(X7767)
      | ~ v2_pre_topc(X7767)
      | ~ l1_pre_topc(X7767)
      | ~ m1_subset_1(X7768,u1_struct_0(X7767))
      | ~ m1_connsp_2(X7769,X7767,X7768)
      | m1_subset_1(X7769,k1_zfmisc_1(u1_struct_0(X7767))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_10,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ( ~ r1_tarski(X35,X36)
        | ~ r2_hidden(X37,X35)
        | r2_hidden(X37,X36) )
      & ( r2_hidden(esk2_2(X38,X39),X38)
        | r1_tarski(X38,X39) )
      & ( ~ r2_hidden(esk2_2(X38,X39),X39)
        | r1_tarski(X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk810_0,k1_zfmisc_1(u1_struct_0(esk809_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk809_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk809_0,esk810_0),esk810_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_connsp_2(esk810_0,esk809_0,esk811_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk809_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk811_0,u1_struct_0(esk809_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk809_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk810_0)
    | ~ r2_hidden(X1,k1_tops_1(esk809_0,esk810_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk811_0,k1_tops_1(esk809_0,esk810_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_13]),c_0_21])]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk811_0,esk810_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
