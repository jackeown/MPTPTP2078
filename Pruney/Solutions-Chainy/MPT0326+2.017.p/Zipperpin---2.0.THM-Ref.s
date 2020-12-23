%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LMRWwrBMiF

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:49 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   55 (  84 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   20
%              Number of atoms          :  381 ( 781 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X8 ) @ ( k2_zfmisc_1 @ X9 @ X10 ) )
      | ( r1_tarski @ X8 @ X10 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
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

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf('24',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['2','24'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X8 ) @ ( k2_zfmisc_1 @ X9 @ X10 ) )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('27',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LMRWwrBMiF
% 0.14/0.38  % Computer   : n024.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 19:16:06 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.39  % Python version: Python 3.6.8
% 0.24/0.39  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 35 iterations in 0.013s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.51  thf(t139_zfmisc_1, conjecture,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.51       ( ![B:$i,C:$i,D:$i]:
% 0.25/0.51         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.25/0.51             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.25/0.51           ( r1_tarski @ B @ D ) ) ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i]:
% 0.25/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.51          ( ![B:$i,C:$i,D:$i]:
% 0.25/0.51            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.25/0.51                ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.25/0.51              ( r1_tarski @ B @ D ) ) ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t139_zfmisc_1])).
% 0.25/0.51  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('1', plain,
% 0.25/0.51      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.25/0.51        | (r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.25/0.51           (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))
% 0.25/0.51         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.25/0.51               (k2_zfmisc_1 @ sk_D @ sk_C))))),
% 0.25/0.51      inference('split', [status(esa)], ['1'])).
% 0.25/0.51  thf('3', plain,
% 0.25/0.51      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))
% 0.25/0.51         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.25/0.51               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.25/0.51      inference('split', [status(esa)], ['1'])).
% 0.25/0.51  thf(t138_zfmisc_1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.51     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.25/0.51       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.25/0.51         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.25/0.51  thf('4', plain,
% 0.25/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.51         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0))
% 0.25/0.51          | ~ (r1_tarski @ (k2_zfmisc_1 @ X7 @ X8) @ (k2_zfmisc_1 @ X9 @ X10))
% 0.25/0.51          | (r1_tarski @ X8 @ X10))),
% 0.25/0.51      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      ((((r1_tarski @ sk_B @ sk_D)
% 0.25/0.51         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.25/0.51         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.25/0.51               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.25/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.51  thf('6', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('7', plain,
% 0.25/0.51      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.25/0.51         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.25/0.51               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.25/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.25/0.51  thf(t113_zfmisc_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.25/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.25/0.51  thf('8', plain,
% 0.25/0.51      (![X4 : $i, X5 : $i]:
% 0.25/0.51         (((X4) = (k1_xboole_0))
% 0.25/0.51          | ((X5) = (k1_xboole_0))
% 0.25/0.51          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 0.25/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.25/0.51  thf('9', plain,
% 0.25/0.51      (((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.51         | ((sk_A) = (k1_xboole_0))
% 0.25/0.51         | ((sk_B) = (k1_xboole_0))))
% 0.25/0.51         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.25/0.51               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.25/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.25/0.51  thf('10', plain,
% 0.25/0.51      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.25/0.51         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.25/0.51               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.25/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.25/0.51  thf('11', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('12', plain,
% 0.25/0.51      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0))))
% 0.25/0.51         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.25/0.51               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.25/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.25/0.51  thf('13', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.25/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.25/0.51  thf('14', plain,
% 0.25/0.51      ((((sk_A) = (k1_xboole_0)))
% 0.25/0.51         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.25/0.51               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.25/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.51  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('16', plain,
% 0.25/0.51      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.25/0.51         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.25/0.51               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.25/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.51  thf('17', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.25/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.25/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.25/0.51  thf('18', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.25/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.25/0.51  thf(t69_xboole_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.25/0.51       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.25/0.51  thf('19', plain,
% 0.25/0.51      (![X2 : $i, X3 : $i]:
% 0.25/0.51         (~ (r1_xboole_0 @ X2 @ X3)
% 0.25/0.51          | ~ (r1_tarski @ X2 @ X3)
% 0.25/0.51          | (v1_xboole_0 @ X2))),
% 0.25/0.51      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.25/0.51  thf('20', plain,
% 0.25/0.51      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.51  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.51      inference('sup-', [status(thm)], ['17', '20'])).
% 0.25/0.51  thf('22', plain,
% 0.25/0.51      (~
% 0.25/0.51       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.25/0.51      inference('demod', [status(thm)], ['16', '21'])).
% 0.25/0.51  thf('23', plain,
% 0.25/0.51      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))) | 
% 0.25/0.51       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.25/0.51      inference('split', [status(esa)], ['1'])).
% 0.25/0.51  thf('24', plain,
% 0.25/0.51      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.25/0.51      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 0.25/0.51  thf('25', plain,
% 0.25/0.51      ((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))),
% 0.25/0.51      inference('simpl_trail', [status(thm)], ['2', '24'])).
% 0.25/0.51  thf('26', plain,
% 0.25/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.51         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0))
% 0.25/0.51          | ~ (r1_tarski @ (k2_zfmisc_1 @ X7 @ X8) @ (k2_zfmisc_1 @ X9 @ X10))
% 0.25/0.51          | (r1_tarski @ X7 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.25/0.51  thf('27', plain,
% 0.25/0.51      (((r1_tarski @ sk_B @ sk_D)
% 0.25/0.51        | ((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.25/0.51  thf('28', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('29', plain, (((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.25/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.25/0.51  thf('30', plain,
% 0.25/0.51      (![X4 : $i, X5 : $i]:
% 0.25/0.51         (((X4) = (k1_xboole_0))
% 0.25/0.51          | ((X5) = (k1_xboole_0))
% 0.25/0.51          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 0.25/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.25/0.51  thf('31', plain,
% 0.25/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.51        | ((sk_B) = (k1_xboole_0))
% 0.25/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.25/0.51  thf('32', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.25/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.25/0.51  thf('33', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('34', plain,
% 0.25/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.25/0.51  thf('35', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.25/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.25/0.51  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.25/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.25/0.51  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.51      inference('sup-', [status(thm)], ['17', '20'])).
% 0.25/0.51  thf('38', plain, ($false),
% 0.25/0.51      inference('demod', [status(thm)], ['0', '36', '37'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.36/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
