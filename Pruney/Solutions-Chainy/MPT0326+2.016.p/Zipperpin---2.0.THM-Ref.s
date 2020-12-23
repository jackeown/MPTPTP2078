%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sJHYF8bwQr

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 (  86 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   20
%              Number of atoms          :  395 ( 809 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t139_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
         => ( r1_tarski @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i,C: $i,D: $i] :
            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
              | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
           => ( r1_tarski @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_zfmisc_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X8 @ X9 ) @ ( k2_zfmisc_1 @ X10 @ X11 ) )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('5',plain,
    ( ( ( r1_tarski @ sk_B @ sk_D )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X6 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf('25',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['2','25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X8 @ X9 ) @ ( k2_zfmisc_1 @ X10 @ X11 ) )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X6 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','21'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sJHYF8bwQr
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:23:12 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.33  % Running portfolio for 600 s
% 0.19/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.33  % Number of cores: 8
% 0.19/0.33  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 35 iterations in 0.020s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(t139_zfmisc_1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.46       ( ![B:$i,C:$i,D:$i]:
% 0.19/0.46         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.19/0.46             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.19/0.46           ( r1_tarski @ B @ D ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.46          ( ![B:$i,C:$i,D:$i]:
% 0.19/0.46            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.19/0.46                ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.19/0.46              ( r1_tarski @ B @ D ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t139_zfmisc_1])).
% 0.19/0.46  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.19/0.46        | (r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.19/0.46           (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))
% 0.19/0.46         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.19/0.46               (k2_zfmisc_1 @ sk_D @ sk_C))))),
% 0.19/0.46      inference('split', [status(esa)], ['1'])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))
% 0.19/0.46         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.46               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.19/0.46      inference('split', [status(esa)], ['1'])).
% 0.19/0.46  thf(t138_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.19/0.46       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.46         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.46         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0))
% 0.19/0.46          | ~ (r1_tarski @ (k2_zfmisc_1 @ X8 @ X9) @ (k2_zfmisc_1 @ X10 @ X11))
% 0.19/0.46          | (r1_tarski @ X9 @ X11))),
% 0.19/0.46      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      ((((r1_tarski @ sk_B @ sk_D)
% 0.19/0.46         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.19/0.46         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.46               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf('6', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.19/0.46         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.46               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.19/0.46      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf(t113_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X5 : $i, X6 : $i]:
% 0.19/0.46         (((X5) = (k1_xboole_0))
% 0.19/0.46          | ((X6) = (k1_xboole_0))
% 0.19/0.46          | ((k2_zfmisc_1 @ X6 @ X5) != (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.46         | ((sk_A) = (k1_xboole_0))
% 0.19/0.46         | ((sk_B) = (k1_xboole_0))))
% 0.19/0.46         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.46               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.19/0.46         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.46               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.19/0.46      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.46  thf('11', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0))))
% 0.19/0.46         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.46               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.46  thf('13', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      ((((sk_A) = (k1_xboole_0)))
% 0.19/0.46         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.46               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.19/0.46      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.19/0.46         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.46               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.46  thf('17', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.46  thf('18', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.19/0.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.46  thf(t68_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.19/0.46       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.19/0.46            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.46         (~ (r1_xboole_0 @ X2 @ X3)
% 0.19/0.46          | (v1_xboole_0 @ X4)
% 0.19/0.46          | ~ (r1_tarski @ X4 @ X2)
% 0.19/0.46          | ~ (r1_tarski @ X4 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.19/0.46          | ~ (r1_tarski @ X1 @ X0)
% 0.19/0.46          | (v1_xboole_0 @ X1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.19/0.46      inference('condensation', [status(thm)], ['20'])).
% 0.19/0.46  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.46      inference('sup-', [status(thm)], ['17', '21'])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (~
% 0.19/0.46       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.19/0.46      inference('demod', [status(thm)], ['16', '22'])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))) | 
% 0.19/0.46       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.19/0.46      inference('split', [status(esa)], ['1'])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.19/0.46      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      ((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))),
% 0.19/0.46      inference('simpl_trail', [status(thm)], ['2', '25'])).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.46         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0))
% 0.19/0.46          | ~ (r1_tarski @ (k2_zfmisc_1 @ X8 @ X9) @ (k2_zfmisc_1 @ X10 @ X11))
% 0.19/0.46          | (r1_tarski @ X8 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.19/0.46  thf('28', plain,
% 0.19/0.46      (((r1_tarski @ sk_B @ sk_D)
% 0.19/0.46        | ((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.46  thf('29', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('30', plain, (((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.19/0.46      inference('clc', [status(thm)], ['28', '29'])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      (![X5 : $i, X6 : $i]:
% 0.19/0.46         (((X5) = (k1_xboole_0))
% 0.19/0.46          | ((X6) = (k1_xboole_0))
% 0.19/0.46          | ((k2_zfmisc_1 @ X6 @ X5) != (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.46  thf('32', plain,
% 0.19/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.46        | ((sk_B) = (k1_xboole_0))
% 0.19/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.46  thf('33', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.46  thf('34', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('35', plain,
% 0.19/0.46      ((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.46  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.46  thf('37', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.46  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.46      inference('sup-', [status(thm)], ['17', '21'])).
% 0.19/0.46  thf('39', plain, ($false),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '37', '38'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
