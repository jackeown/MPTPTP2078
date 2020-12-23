%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TlQNsKpANU

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 135 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  570 (1418 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D ) ),
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X7
        = ( k4_tarski @ ( sk_E @ X7 @ X6 @ X5 ) @ ( sk_F @ X7 @ X6 @ X5 ) ) )
      | ~ ( r2_hidden @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X3
        = ( k4_tarski @ ( sk_E @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ ( sk_F @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ ( sk_F @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_E @ X7 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('18',plain,
    ( ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
    = ( k4_tarski @ ( sk_E @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B ) @ ( sk_F @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_mcart_1 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( sk_E @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B ) @ ( sk_F @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B ) @ X0 )
      = ( k4_tarski @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('23',plain,(
    r2_hidden @ ( sk_E @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_B )
      | ~ ( r2_hidden @ X15 @ sk_C_1 )
      | ( sk_A
       != ( k3_mcart_1 @ X14 @ X15 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( sk_A
       != ( k3_mcart_1 @ ( sk_E @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_F @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_F @ X7 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_F @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_D ) ),
    inference('sup-',[status(thm)],['9','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k3_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_F @ sk_A @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) @ sk_D ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TlQNsKpANU
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 62 iterations in 0.053s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.20/0.53  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(t72_mcart_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ~( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) ) & 
% 0.20/0.53          ( ![E:$i,F:$i,G:$i]:
% 0.20/0.53            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.53                 ( r2_hidden @ G @ D ) & ( ( A ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53        ( ~( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) ) & 
% 0.20/0.53             ( ![E:$i,F:$i,G:$i]:
% 0.20/0.53               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.53                    ( r2_hidden @ G @ D ) & 
% 0.20/0.53                    ( ( A ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t72_mcart_1])).
% 0.20/0.53  thf('0', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d3_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.53       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.53  thf(t103_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.53          ( r2_hidden @ D @ A ) & 
% 0.20/0.53          ( ![E:$i,F:$i]:
% 0.20/0.53            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.53                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X4 @ (k2_zfmisc_1 @ X5 @ X6))
% 0.20/0.53          | ((X7) = (k4_tarski @ (sk_E @ X7 @ X6 @ X5) @ (sk_F @ X7 @ X6 @ X5)))
% 0.20/0.53          | ~ (r2_hidden @ X7 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.53          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.53          | ((X3)
% 0.20/0.53              = (k4_tarski @ (sk_E @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ 
% 0.20/0.53                 (sk_F @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (((sk_A)
% 0.20/0.53         = (k4_tarski @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53            (sk_F @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '8'])).
% 0.20/0.53  thf('10', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X4 @ (k2_zfmisc_1 @ X5 @ X6))
% 0.20/0.53          | (r2_hidden @ (sk_E @ X7 @ X6 @ X5) @ X5)
% 0.20/0.53          | ~ (r2_hidden @ X7 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.53          | (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.53          | (r2_hidden @ (sk_E @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ 
% 0.20/0.53             (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((r2_hidden @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53        (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.53          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1))
% 0.20/0.53         = (k4_tarski @ 
% 0.20/0.53            (sk_E @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53             sk_C_1 @ sk_B) @ 
% 0.20/0.53            (sk_F @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53             sk_C_1 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf(d3_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         ((k3_mcart_1 @ X8 @ X9 @ X10)
% 0.20/0.53           = (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_mcart_1 @ 
% 0.20/0.53           (sk_E @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53            sk_C_1 @ sk_B) @ 
% 0.20/0.53           (sk_F @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53            sk_C_1 @ sk_B) @ 
% 0.20/0.53           X0)
% 0.20/0.53           = (k4_tarski @ 
% 0.20/0.53              (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((r2_hidden @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53        (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.53          | (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((r2_hidden @ 
% 0.20/0.53        (sk_E @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53         sk_C_1 @ sk_B) @ 
% 0.20/0.53        sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X14 @ sk_B)
% 0.20/0.53          | ~ (r2_hidden @ X15 @ sk_C_1)
% 0.20/0.53          | ((sk_A) != (k3_mcart_1 @ X14 @ X15 @ X16))
% 0.20/0.53          | ~ (r2_hidden @ X16 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ sk_D)
% 0.20/0.53          | ((sk_A)
% 0.20/0.53              != (k3_mcart_1 @ 
% 0.20/0.53                  (sk_E @ 
% 0.20/0.53                   (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53                   sk_C_1 @ sk_B) @ 
% 0.20/0.53                  X1 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_A)
% 0.20/0.53            != (k4_tarski @ 
% 0.20/0.53                (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ X0))
% 0.20/0.53          | ~ (r2_hidden @ 
% 0.20/0.53               (sk_F @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53                sk_C_1 @ sk_B) @ 
% 0.20/0.53               sk_C_1)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((r2_hidden @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53        (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.53  thf('28', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X4 @ (k2_zfmisc_1 @ X5 @ X6))
% 0.20/0.53          | (r2_hidden @ (sk_F @ X7 @ X6 @ X5) @ X6)
% 0.20/0.53          | ~ (r2_hidden @ X7 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.53          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((r2_hidden @ 
% 0.20/0.53        (sk_F @ (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ 
% 0.20/0.53         sk_C_1 @ sk_B) @ 
% 0.20/0.53        sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_A)
% 0.20/0.53            != (k4_tarski @ 
% 0.20/0.53                (sk_E @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((sk_A) != (sk_A))
% 0.20/0.53        | ~ (r2_hidden @ 
% 0.20/0.53             (sk_F @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '32'])).
% 0.20/0.53  thf('34', plain, ((r2_hidden @ sk_A @ (k3_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.53          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.53          | (r2_hidden @ (sk_F @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((r2_hidden @ (sk_F @ sk_A @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) @ sk_D)),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.53  thf('39', plain, (((sk_A) != (sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '38'])).
% 0.20/0.53  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
