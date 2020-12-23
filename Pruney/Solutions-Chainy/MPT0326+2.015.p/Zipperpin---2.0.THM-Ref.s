%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0a71bsJAxQ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  89 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :   19
%              Number of atoms          :  415 ( 837 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ( r1_tarski @ X11 @ X13 ) ) ),
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

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
        | ( r1_tarski @ sk_B @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','22'])).

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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0a71bsJAxQ
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 33 iterations in 0.017s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(t139_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i,C:$i,D:$i]:
% 0.21/0.47         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.21/0.47             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.21/0.47           ( r1_tarski @ B @ D ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47          ( ![B:$i,C:$i,D:$i]:
% 0.21/0.47            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.21/0.47                ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.21/0.47              ( r1_tarski @ B @ D ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t139_zfmisc_1])).
% 0.21/0.47  thf('0', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.21/0.47        | (r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.21/0.47           (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))
% 0.21/0.47         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.21/0.47               (k2_zfmisc_1 @ sk_D @ sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['1'])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))
% 0.21/0.47         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.47      inference('split', [status(esa)], ['1'])).
% 0.21/0.47  thf(t138_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.21/0.47       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.47         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.21/0.47          | ~ (r1_tarski @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 0.21/0.47               (k2_zfmisc_1 @ X12 @ X13))
% 0.21/0.47          | (r1_tarski @ X11 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((((r1_tarski @ sk_B @ sk_D)
% 0.21/0.47         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.21/0.47         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.47         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf(t117_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.21/0.47            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.21/0.47          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.47         (((X7) = (k1_xboole_0))
% 0.21/0.47          | (r1_tarski @ X8 @ X9)
% 0.21/0.47          | ~ (r1_tarski @ (k2_zfmisc_1 @ X7 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((![X0 : $i]:
% 0.21/0.47          (~ (r1_tarski @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0))
% 0.21/0.47           | (r1_tarski @ sk_B @ X0)
% 0.21/0.47           | ((sk_A) = (k1_xboole_0))))
% 0.21/0.47         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('10', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      ((![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.47         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.21/0.47         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf(t79_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X6)),
% 0.21/0.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.47  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf(t69_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.47       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (r1_xboole_0 @ X3 @ X4)
% 0.21/0.47          | ~ (r1_tarski @ X3 @ X4)
% 0.21/0.47          | (v1_xboole_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (~
% 0.21/0.47       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))) | 
% 0.21/0.47       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('split', [status(esa)], ['1'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      ((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['2', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.47         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.21/0.47          | ~ (r1_tarski @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 0.21/0.47               (k2_zfmisc_1 @ X12 @ X13))
% 0.21/0.47          | (r1_tarski @ X10 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (((r1_tarski @ sk_B @ sk_D)
% 0.21/0.47        | ((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('29', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('30', plain, (((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.47      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.47         (((X7) = (k1_xboole_0))
% 0.21/0.47          | (r1_tarski @ X8 @ X9)
% 0.21/0.47          | ~ (r1_tarski @ (k2_zfmisc_1 @ X7 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r1_tarski @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ X0))
% 0.21/0.47          | (r1_tarski @ sk_A @ X0)
% 0.21/0.47          | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.47  thf('33', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('36', plain, ((((sk_B) = (k1_xboole_0)) | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('38', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('40', plain, ($false),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '38', '39'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
