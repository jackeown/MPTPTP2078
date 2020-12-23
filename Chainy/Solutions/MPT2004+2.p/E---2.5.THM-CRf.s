%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2004+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 12.71s
% Output     : CNFRefutation 12.71s
% Verified   : 
% Statistics : Number of formulae       :    9 (  18 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    1 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 ( 102 expanded)
%              Number of equality atoms :    8 (  26 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_waybel_9,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                 => ( ( u1_struct_0(X1) = u1_struct_0(X2)
                      & X3 = X4
                      & m1_setfam_1(X3,u1_struct_0(X1)) )
                   => m1_setfam_1(X4,u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_9)).

fof(c_0_1,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_struct_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( ( u1_struct_0(X1) = u1_struct_0(X2)
                        & X3 = X4
                        & m1_setfam_1(X3,u1_struct_0(X1)) )
                     => m1_setfam_1(X4,u1_struct_0(X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_waybel_9])).

fof(c_0_2,negated_conjecture,
    ( l1_struct_0(esk1663_0)
    & l1_struct_0(esk1664_0)
    & m1_subset_1(esk1665_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1663_0))))
    & m1_subset_1(esk1666_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1664_0))))
    & u1_struct_0(esk1663_0) = u1_struct_0(esk1664_0)
    & esk1665_0 = esk1666_0
    & m1_setfam_1(esk1665_0,u1_struct_0(esk1663_0))
    & ~ m1_setfam_1(esk1666_0,u1_struct_0(esk1664_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_1])])])).

cnf(c_0_3,negated_conjecture,
    ( m1_setfam_1(esk1665_0,u1_struct_0(esk1663_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_4,negated_conjecture,
    ( esk1665_0 = esk1666_0 ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_5,negated_conjecture,
    ( ~ m1_setfam_1(esk1666_0,u1_struct_0(esk1664_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_6,negated_conjecture,
    ( u1_struct_0(esk1663_0) = u1_struct_0(esk1664_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_7,negated_conjecture,
    ( m1_setfam_1(esk1666_0,u1_struct_0(esk1663_0)) ),
    inference(rw,[status(thm)],[c_0_3,c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_5,c_0_6]),c_0_7])]),
    [proof]).
%------------------------------------------------------------------------------
