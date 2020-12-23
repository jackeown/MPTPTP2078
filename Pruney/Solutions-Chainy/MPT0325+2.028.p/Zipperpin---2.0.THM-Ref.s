%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Cr2r0eDcw

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  99 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   18
%              Number of atoms          :  419 ( 871 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X12 ) )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_D )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','32'])).

thf('34',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['16','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['14','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('40',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','40','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Cr2r0eDcw
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:40:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 69 iterations in 0.037s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(t138_zfmisc_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.20/0.46       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.46         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.20/0.46          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.46            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.46  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d3_tarski, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf(l54_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.46       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.46         ((r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X12))
% 0.20/0.46          | ~ (r2_hidden @ X10 @ X12)
% 0.20/0.46          | ~ (r2_hidden @ X8 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ X1)
% 0.20/0.46          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.46          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.20/0.46             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ X1)
% 0.20/0.46          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.20/0.46             (k2_zfmisc_1 @ X0 @ X2))
% 0.20/0.46          | (r1_tarski @ X2 @ X3))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.46          | (r2_hidden @ X0 @ X2)
% 0.20/0.46          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.20/0.46          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ sk_B @ X0)
% 0.20/0.46          | (r1_tarski @ sk_A @ X1)
% 0.20/0.46          | (r2_hidden @ 
% 0.20/0.46             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.20/0.46             (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         ((r2_hidden @ X10 @ X11)
% 0.20/0.46          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.20/0.46      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ sk_A @ X1)
% 0.20/0.46          | (r1_tarski @ sk_B @ X0)
% 0.20/0.46          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_D))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_tarski @ sk_B @ sk_D)
% 0.20/0.46          | (r1_tarski @ sk_A @ X0)
% 0.20/0.46          | (r1_tarski @ sk_B @ sk_D))),
% 0.20/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_B @ sk_D))),
% 0.20/0.46      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.20/0.46      inference('split', [status(esa)], ['15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ sk_B @ X0)
% 0.20/0.46          | (r1_tarski @ sk_A @ X1)
% 0.20/0.46          | (r2_hidden @ 
% 0.20/0.46             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.20/0.46             (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         ((r2_hidden @ X8 @ X9)
% 0.20/0.46          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.20/0.46      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ sk_A @ X1)
% 0.20/0.46          | (r1_tarski @ sk_B @ X0)
% 0.20/0.46          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_C_1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_tarski @ sk_B @ X0)
% 0.20/0.46          | (r1_tarski @ sk_A @ sk_C_1)
% 0.20/0.46          | (r1_tarski @ sk_A @ sk_C_1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X0 : $i]: ((r1_tarski @ sk_A @ sk_C_1) | (r1_tarski @ sk_B @ X0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.20/0.46      inference('split', [status(esa)], ['15'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 0.20/0.46         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.46  thf('25', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.46  thf(d10_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (![X4 : $i, X6 : $i]:
% 0.20/0.46         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.46  thf('29', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.46         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.46  thf(t113_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (![X14 : $i, X15 : $i]:
% 0.20/0.46         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.20/0.46          | ((X15) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.20/0.46      inference('demod', [status(thm)], ['30', '32'])).
% 0.20/0.46  thf('34', plain, (((r1_tarski @ sk_A @ sk_C_1))),
% 0.20/0.46      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C_1))),
% 0.20/0.46      inference('split', [status(esa)], ['15'])).
% 0.20/0.46  thf('36', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['34', '35'])).
% 0.20/0.46  thf('37', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['16', '36'])).
% 0.20/0.46  thf('38', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.20/0.46      inference('clc', [status(thm)], ['14', '37'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.46  thf('40', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.46  thf('41', plain,
% 0.20/0.46      (![X14 : $i, X15 : $i]:
% 0.20/0.46         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.20/0.46          | ((X14) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.46  thf('42', plain,
% 0.20/0.46      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.46  thf('43', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '40', '42'])).
% 0.20/0.46  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
