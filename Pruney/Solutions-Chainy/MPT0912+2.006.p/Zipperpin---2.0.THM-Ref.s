%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3twvOP9Mwd

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 166 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  491 (1707 expanded)
%              Number of equality atoms :   39 ( 113 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

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
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('10',plain,(
    ! [X12: $i,X14: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X12 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,
    ( ( k2_mcart_1 @ sk_A )
    = ( sk_E @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('19',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('22',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( sk_D @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('25',plain,(
    ! [X12: $i,X14: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X12 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('32',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_B )
      | ~ ( r2_hidden @ X16 @ sk_C )
      | ( sk_A
       != ( k3_mcart_1 @ X15 @ X16 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('38',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','39'])).

thf('41',plain,(
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3twvOP9Mwd
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 39 iterations in 0.022s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i).
% 0.20/0.48  thf(t72_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ~( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) ) & 
% 0.20/0.48          ( ![E:$i,F:$i,G:$i]:
% 0.20/0.48            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.48                 ( r2_hidden @ G @ D ) & ( ( A ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ~( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) ) & 
% 0.20/0.48             ( ![E:$i,F:$i,G:$i]:
% 0.20/0.48               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.48                    ( r2_hidden @ G @ D ) & 
% 0.20/0.48                    ( ( A ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t72_mcart_1])).
% 0.20/0.48  thf('0', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d3_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf(l139_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.48          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.48          | ((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf('5', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf(t7_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]: ((k1_mcart_1 @ (k4_tarski @ X12 @ X13)) = (X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('7', plain, (((k1_mcart_1 @ sk_A) = (sk_D @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '7'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X12 : $i, X14 : $i]: ((k2_mcart_1 @ (k4_tarski @ X12 @ X14)) = (X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('11', plain, (((k2_mcart_1 @ sk_A) = (sk_E @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.48  thf('13', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf(t10_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((r2_hidden @ (k1_mcart_1 @ X9) @ X10)
% 0.20/0.48          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.48          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.48         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.48         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]: ((k1_mcart_1 @ (k4_tarski @ X12 @ X13)) = (X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((k1_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_D @ (k1_mcart_1 @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.48         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.48         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X12 : $i, X14 : $i]: ((k2_mcart_1 @ (k4_tarski @ X12 @ X14)) = (X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((k2_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_E @ (k1_mcart_1 @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.48         (k2_mcart_1 @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '26'])).
% 0.20/0.48  thf(d3_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.20/0.48           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.48           (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X0)
% 0.20/0.48           = (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((r2_hidden @ (k1_mcart_1 @ X9) @ X10)
% 0.20/0.48          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('32', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X15 @ sk_B)
% 0.20/0.48          | ~ (r2_hidden @ X16 @ sk_C)
% 0.20/0.48          | ((sk_A) != (k3_mcart_1 @ X15 @ X16 @ X17))
% 0.20/0.48          | ~ (r2_hidden @ X17 @ sk_D_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ sk_D_1)
% 0.20/0.48          | ((sk_A)
% 0.20/0.48              != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.20/0.48          | ~ (r2_hidden @ X1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.20/0.48          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_C)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((r2_hidden @ (k2_mcart_1 @ X9) @ X11)
% 0.20/0.48          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('38', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['35', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '39'])).
% 0.20/0.48  thf('41', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((r2_hidden @ (k2_mcart_1 @ X9) @ X11)
% 0.20/0.48          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.48          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1)),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.48  thf('46', plain, (((sk_A) != (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['40', '45'])).
% 0.20/0.48  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
