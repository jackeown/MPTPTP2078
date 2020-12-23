%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1kaGi36ZC1

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:03 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   76 (1023 expanded)
%              Number of leaves         :   19 ( 323 expanded)
%              Depth                    :   22
%              Number of atoms          :  575 (11219 expanded)
%              Number of equality atoms :   43 ( 904 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
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
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
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

thf('14',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['8','11'])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('21',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( sk_D @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('27',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('28',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_mcart_1 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('33',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_B ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_B )
      | ~ ( r2_hidden @ X18 @ sk_C )
      | ( sk_A
       != ( k3_mcart_1 @ X17 @ X18 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('41',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_C ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','45'])).

thf('47',plain,(
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['8','11'])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['46','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1kaGi36ZC1
% 0.15/0.37  % Computer   : n004.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 12:53:24 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 116 iterations in 0.060s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.54  thf(sk_E_type, type, sk_E: $i > $i).
% 0.23/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.23/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.23/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.23/0.54  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.23/0.54  thf(sk_D_type, type, sk_D: $i > $i).
% 0.23/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.54  thf(t72_mcart_1, conjecture,
% 0.23/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.54     ( ~( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) ) & 
% 0.23/0.54          ( ![E:$i,F:$i,G:$i]:
% 0.23/0.54            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.23/0.54                 ( r2_hidden @ G @ D ) & ( ( A ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.54        ( ~( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) ) & 
% 0.23/0.54             ( ![E:$i,F:$i,G:$i]:
% 0.23/0.54               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.23/0.54                    ( r2_hidden @ G @ D ) & 
% 0.23/0.54                    ( ( A ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t72_mcart_1])).
% 0.23/0.54  thf('0', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d3_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.23/0.54       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.54         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.23/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.54  thf(l139_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.23/0.54          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.23/0.54          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.54          | ((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.54  thf('4', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['0', '3'])).
% 0.23/0.54  thf('5', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['0', '3'])).
% 0.23/0.54  thf(t7_mcart_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.23/0.54       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.23/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.54  thf('7', plain, (((k1_mcart_1 @ sk_A) = (sk_D @ sk_A))),
% 0.23/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['4', '7'])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['4', '7'])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.54  thf('11', plain, (((k2_mcart_1 @ sk_A) = (sk_E @ sk_A))),
% 0.23/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['8', '11'])).
% 0.23/0.54  thf('13', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['8', '11'])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.54         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.23/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.54  thf(l54_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.54     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.23/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.54         ((r2_hidden @ X3 @ X4)
% 0.23/0.54          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.54         (~ (r2_hidden @ (k4_tarski @ X4 @ X3) @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.54          | (r2_hidden @ X4 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         (~ (r2_hidden @ sk_A @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.54          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['14', '17'])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.23/0.54      inference('sup-', [status(thm)], ['13', '18'])).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.23/0.54          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.54         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.54  thf('22', plain,
% 0.23/0.54      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.54         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.23/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.54  thf('24', plain,
% 0.23/0.54      (((k1_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_D @ (k1_mcart_1 @ sk_A)))),
% 0.23/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.54         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['21', '24'])).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.54         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['21', '24'])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      (((k2_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_E @ (k1_mcart_1 @ sk_A)))),
% 0.23/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.23/0.54  thf('29', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.54         (k2_mcart_1 @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['25', '28'])).
% 0.23/0.54  thf(d3_mcart_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.23/0.54  thf('30', plain,
% 0.23/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.54         ((k3_mcart_1 @ X8 @ X9 @ X10)
% 0.23/0.54           = (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.54           (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X0)
% 0.23/0.54           = (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.23/0.54      inference('sup+', [status(thm)], ['29', '30'])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.23/0.54      inference('sup-', [status(thm)], ['13', '18'])).
% 0.23/0.54  thf('33', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.54         (k2_mcart_1 @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['25', '28'])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.54         ((r2_hidden @ X3 @ X4)
% 0.23/0.54          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.23/0.54  thf('35', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.54          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.54  thf('36', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_B)),
% 0.23/0.54      inference('sup-', [status(thm)], ['32', '35'])).
% 0.23/0.54  thf('37', plain,
% 0.23/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X17 @ sk_B)
% 0.23/0.54          | ~ (r2_hidden @ X18 @ sk_C)
% 0.23/0.54          | ((sk_A) != (k3_mcart_1 @ X17 @ X18 @ X19))
% 0.23/0.54          | ~ (r2_hidden @ X19 @ sk_D_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('38', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X0 @ sk_D_1)
% 0.23/0.54          | ((sk_A)
% 0.23/0.54              != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.23/0.54          | ~ (r2_hidden @ X1 @ sk_C))),
% 0.23/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.23/0.54  thf('39', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.23/0.54          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_C)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['31', '38'])).
% 0.23/0.54  thf('40', plain,
% 0.23/0.54      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.23/0.54      inference('sup-', [status(thm)], ['13', '18'])).
% 0.23/0.54  thf('41', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.54         (k2_mcart_1 @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['25', '28'])).
% 0.23/0.54  thf('42', plain,
% 0.23/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.54         ((r2_hidden @ X5 @ X6)
% 0.23/0.54          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.23/0.54  thf('43', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.54          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.23/0.54  thf('44', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_C)),
% 0.23/0.54      inference('sup-', [status(thm)], ['40', '43'])).
% 0.23/0.54  thf('45', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.23/0.54          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.23/0.54      inference('demod', [status(thm)], ['39', '44'])).
% 0.23/0.54  thf('46', plain,
% 0.23/0.54      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['12', '45'])).
% 0.23/0.54  thf('47', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('48', plain,
% 0.23/0.54      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['8', '11'])).
% 0.23/0.54  thf('49', plain,
% 0.23/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.54         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.23/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.54  thf('50', plain,
% 0.23/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.54         ((r2_hidden @ X5 @ X6)
% 0.23/0.54          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.23/0.54  thf('51', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.54         (~ (r2_hidden @ (k4_tarski @ X4 @ X3) @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.54          | (r2_hidden @ X3 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.23/0.54  thf('52', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         (~ (r2_hidden @ sk_A @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.54          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['48', '51'])).
% 0.23/0.54  thf('53', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['47', '52'])).
% 0.23/0.54  thf('54', plain, (((sk_A) != (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['46', '53'])).
% 0.23/0.54  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
