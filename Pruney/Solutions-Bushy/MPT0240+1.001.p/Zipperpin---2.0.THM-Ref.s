%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0240+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XDYPf5tu6e

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:33 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 120 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  904 (1975 expanded)
%              Number of equality atoms :   75 ( 175 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(t35_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X14 @ X15 ) @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ( X16
       != ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X14 @ X15 ) @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
        = X2 )
      | ( ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X5 @ X9 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
        = X2 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_E_1 @ ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7
        = ( k4_tarski @ X5 @ X6 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ( ( sk_C @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
        = ( k4_tarski @ ( sk_E_1 @ ( sk_C @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
        = ( k4_tarski @ X0 @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 ) @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
        = X2 )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
        = X2 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
        = X2 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
        = ( k4_tarski @ X0 @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 ) @ X1 @ ( k1_tarski @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 )
        = ( k4_tarski @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 )
        = X2 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 )
        = X2 ) ) ),
    inference('sup+',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 )
        = X2 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 )
        = ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) ) @ X0 )
        = ( k4_tarski @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) ) @ ( k4_tarski @ X2 @ X1 ) )
        = ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k4_tarski @ X1 @ X0 ) )
       != ( k4_tarski @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X10 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( X7
       != ( k4_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ( zip_tseitin_0 @ X6 @ X5 @ ( k4_tarski @ X5 @ X6 ) @ X8 @ X10 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k4_tarski @ X1 @ X0 ) )
       != ( k4_tarski @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k4_tarski @ X1 @ X0 ) )
       != ( k4_tarski @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( sk_C @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) ) @ ( k4_tarski @ X2 @ X1 ) )
        = ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).


%------------------------------------------------------------------------------
