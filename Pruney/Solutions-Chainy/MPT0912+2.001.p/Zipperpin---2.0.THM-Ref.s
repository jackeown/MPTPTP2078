%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5hFl34goMc

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 110 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  554 (1218 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(t72_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) )
        & ! [E: $i,F: $i,G: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( r2_hidden @ G @ D )
              & ( A
                = ( k3_mcart_1 @ E @ F @ G ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) )
          & ! [E: $i,F: $i,G: $i] :
              ~ ( ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C )
                & ( r2_hidden @ G @ D )
                & ( A
                  = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( X6
        = ( k4_tarski @ ( sk_E @ X6 @ X5 @ X4 ) @ ( sk_F @ X6 @ X5 @ X4 ) ) )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X3
        = ( k4_tarski @ ( sk_E @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ ( sk_F @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( sk_F @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_E @ X6 @ X5 @ X4 ) @ X4 )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('16',plain,
    ( ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    = ( k4_tarski @ ( sk_E @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ ( sk_F @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_mcart_1 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( sk_E @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ ( sk_F @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ X0 )
      = ( k4_tarski @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('21',plain,(
    r2_hidden @ ( sk_E @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ sk_B )
      | ~ ( r2_hidden @ X14 @ sk_C )
      | ( sk_A
       != ( k3_mcart_1 @ X13 @ X14 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( sk_A
       != ( k3_mcart_1 @ ( sk_E @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_F @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_F @ X6 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_F @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_D ) ),
    inference('sup-',[status(thm)],['7','30'])).

thf('32',plain,(
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_F @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5hFl34goMc
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:58:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 39 iterations in 0.023s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.20/0.49  thf(t72_mcart_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ~( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) ) & 
% 0.20/0.49          ( ![E:$i,F:$i,G:$i]:
% 0.20/0.49            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.49                 ( r2_hidden @ G @ D ) & ( ( A ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ~( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) ) & 
% 0.20/0.49             ( ![E:$i,F:$i,G:$i]:
% 0.20/0.49               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.49                    ( r2_hidden @ G @ D ) & 
% 0.20/0.49                    ( ( A ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t72_mcart_1])).
% 0.20/0.49  thf('0', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d3_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.49       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf(t103_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.49          ( r2_hidden @ D @ A ) & 
% 0.20/0.49          ( ![E:$i,F:$i]:
% 0.20/0.49            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.49                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X3 @ (k2_zfmisc_1 @ X4 @ X5))
% 0.20/0.49          | ((X6) = (k4_tarski @ (sk_E @ X6 @ X5 @ X4) @ (sk_F @ X6 @ X5 @ X4)))
% 0.20/0.49          | ~ (r2_hidden @ X6 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.49          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X3)
% 0.20/0.49              = (k4_tarski @ (sk_E @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ 
% 0.20/0.49                 (sk_F @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((sk_A)
% 0.20/0.49         = (k4_tarski @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49            (sk_F @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '6'])).
% 0.20/0.49  thf('8', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X3 @ (k2_zfmisc_1 @ X4 @ X5))
% 0.20/0.49          | (r2_hidden @ (sk_E @ X6 @ X5 @ X4) @ X4)
% 0.20/0.49          | ~ (r2_hidden @ X6 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_E @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ 
% 0.20/0.49             (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((r2_hidden @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.49          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.49         = (k4_tarski @ 
% 0.20/0.49            (sk_E @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49             sk_C @ sk_B) @ 
% 0.20/0.49            (sk_F @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49             sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf(d3_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         ((k3_mcart_1 @ X7 @ X8 @ X9)
% 0.20/0.49           = (k4_tarski @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k3_mcart_1 @ 
% 0.20/0.49           (sk_E @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ sk_C @ 
% 0.20/0.49            sk_B) @ 
% 0.20/0.49           (sk_F @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ sk_C @ 
% 0.20/0.49            sk_B) @ 
% 0.20/0.49           X0)
% 0.20/0.49           = (k4_tarski @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49              X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((r2_hidden @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((r2_hidden @ 
% 0.20/0.49        (sk_E @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ sk_C @ 
% 0.20/0.49         sk_B) @ 
% 0.20/0.49        sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X13 @ sk_B)
% 0.20/0.49          | ~ (r2_hidden @ X14 @ sk_C)
% 0.20/0.49          | ((sk_A) != (k3_mcart_1 @ X13 @ X14 @ X15))
% 0.20/0.49          | ~ (r2_hidden @ X15 @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ sk_D)
% 0.20/0.49          | ((sk_A)
% 0.20/0.49              != (k3_mcart_1 @ 
% 0.20/0.49                  (sk_E @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49                   sk_C @ sk_B) @ 
% 0.20/0.49                  X1 @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_A)
% 0.20/0.49            != (k4_tarski @ 
% 0.20/0.49                (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ X0))
% 0.20/0.49          | ~ (r2_hidden @ 
% 0.20/0.49               (sk_F @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49                sk_C @ sk_B) @ 
% 0.20/0.49               sk_C)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((r2_hidden @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.49  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X3 @ (k2_zfmisc_1 @ X4 @ X5))
% 0.20/0.49          | (r2_hidden @ (sk_F @ X6 @ X5 @ X4) @ X5)
% 0.20/0.49          | ~ (r2_hidden @ X6 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((r2_hidden @ 
% 0.20/0.49        (sk_F @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ sk_C @ 
% 0.20/0.49         sk_B) @ 
% 0.20/0.49        sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_A)
% 0.20/0.49            != (k4_tarski @ 
% 0.20/0.49                (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((((sk_A) != (sk_A))
% 0.20/0.49        | ~ (r2_hidden @ (sk_F @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.20/0.49             sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '30'])).
% 0.20/0.49  thf('32', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_F @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((r2_hidden @ (sk_F @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ sk_D)),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.49  thf('37', plain, (((sk_A) != (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['31', '36'])).
% 0.20/0.49  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
