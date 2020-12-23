%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0403+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ufo5ySgaaG

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:51 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  390 ( 651 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_setfam_1_type,type,(
    k2_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t29_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t29_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ ( k2_setfam_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( k2_xboole_0 @ X21 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(d4_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k2_xboole_0 @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k2_xboole_0 @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X10 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( X7
       != ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ( zip_tseitin_0 @ X6 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) @ X8 @ X10 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ X3 @ ( k2_xboole_0 @ X3 @ ( sk_C @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X3 @ X2 ) @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ X2 @ X0 )
      | ( r1_setfam_1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 )
      | ( r1_setfam_1 @ X0 @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k2_setfam_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k2_setfam_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(reflexivity_r1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_setfam_1 @ A @ A ) )).

thf('13',plain,(
    ! [X22: $i] :
      ( r1_setfam_1 @ X22 @ X22 ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X22: $i] :
      ( r1_setfam_1 @ X22 @ X22 ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r1_setfam_1 @ ( k2_setfam_1 @ X0 @ X0 ) @ X2 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r1_tarski @ ( sk_C @ X3 @ X2 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) )
      | ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).


%------------------------------------------------------------------------------
