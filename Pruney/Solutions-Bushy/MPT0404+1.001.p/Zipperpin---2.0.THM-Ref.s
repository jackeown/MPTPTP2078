%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0404+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.URb5WjvNlr

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  334 ( 434 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k3_setfam_1_type,type,(
    k3_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t30_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_setfam_1 @ ( k3_setfam_1 @ A @ A ) @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_setfam_1 @ ( k3_setfam_1 @ A @ A ) @ A ) ),
    inference('cnf.neg',[status(esa)],[t30_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ ( k3_setfam_1 @ sk_A @ sk_A ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(d5_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k3_xboole_0 @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k3_xboole_0 @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X14 @ X15 ) @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ( X16
       != ( k3_setfam_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X14 @ X15 ) @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k3_setfam_1 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X5 @ X9 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ ( sk_F_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) )
      | ( r1_setfam_1 @ ( k3_setfam_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r1_tarski @ ( sk_C @ X3 @ X2 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X2 )
      | ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X2 )
      | ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X0 )
      | ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['0','16'])).


%------------------------------------------------------------------------------
