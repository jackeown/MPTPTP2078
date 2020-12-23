%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7EaLEXIQwR

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:34 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  320 ( 561 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ X20 )
      | ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('12',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('26',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('31',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7EaLEXIQwR
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.60  % Solved by: fo/fo7.sh
% 0.35/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.60  % done 295 iterations in 0.138s
% 0.35/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.60  % SZS output start Refutation
% 0.35/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.60  thf(t149_zfmisc_1, conjecture,
% 0.35/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.60     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.35/0.60         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.35/0.60       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.35/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.60        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.35/0.60            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.35/0.60          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.35/0.60    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.35/0.60  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(symmetry_r1_xboole_0, axiom,
% 0.35/0.60    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.35/0.60  thf('2', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.35/0.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.35/0.60  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.35/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.60  thf('4', plain,
% 0.35/0.60      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(l27_zfmisc_1, axiom,
% 0.35/0.60    (![A:$i,B:$i]:
% 0.35/0.60     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.35/0.60  thf('5', plain,
% 0.35/0.60      (![X19 : $i, X20 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ (k1_tarski @ X19) @ X20) | (r2_hidden @ X19 @ X20))),
% 0.35/0.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.35/0.60  thf(t83_xboole_1, axiom,
% 0.35/0.60    (![A:$i,B:$i]:
% 0.35/0.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.60  thf('6', plain,
% 0.35/0.60      (![X15 : $i, X16 : $i]:
% 0.35/0.60         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.35/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.35/0.60  thf('7', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         ((r2_hidden @ X1 @ X0)
% 0.35/0.60          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.60  thf(t106_xboole_1, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.35/0.60       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.35/0.60  thf('8', plain,
% 0.35/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ X6 @ X8)
% 0.35/0.60          | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.35/0.60      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.35/0.60  thf('9', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.60         (~ (r1_tarski @ X2 @ (k1_tarski @ X0))
% 0.35/0.60          | (r2_hidden @ X0 @ X1)
% 0.35/0.60          | (r1_xboole_0 @ X2 @ X1))),
% 0.35/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.60  thf('10', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.35/0.60          | (r2_hidden @ sk_D @ X0))),
% 0.35/0.60      inference('sup-', [status(thm)], ['4', '9'])).
% 0.35/0.60  thf(t75_xboole_1, axiom,
% 0.35/0.60    (![A:$i,B:$i]:
% 0.35/0.60     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.35/0.60          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.35/0.60  thf('11', plain,
% 0.35/0.60      (![X13 : $i, X14 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ X13 @ X14)
% 0.35/0.60          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X14))),
% 0.35/0.60      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.35/0.60  thf('12', plain, (((r2_hidden @ sk_D @ sk_B) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.60  thf('13', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.35/0.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.35/0.60  thf('14', plain, (((r2_hidden @ sk_D @ sk_B) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.60  thf('15', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.35/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.60  thf(t70_xboole_1, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.35/0.60            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.35/0.60       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.35/0.60            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.35/0.60  thf('16', plain,
% 0.35/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.35/0.60          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.35/0.60          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.35/0.60      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.35/0.60  thf('17', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.35/0.60          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.60  thf('18', plain,
% 0.35/0.60      (((r2_hidden @ sk_D @ sk_B)
% 0.35/0.60        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['14', '17'])).
% 0.35/0.60  thf('19', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('20', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(t3_xboole_0, axiom,
% 0.35/0.60    (![A:$i,B:$i]:
% 0.35/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.35/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.35/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.35/0.60  thf('21', plain,
% 0.35/0.60      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.35/0.60         (~ (r2_hidden @ X4 @ X2)
% 0.35/0.60          | ~ (r2_hidden @ X4 @ X5)
% 0.35/0.60          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.35/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.35/0.60  thf('22', plain,
% 0.35/0.60      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.35/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.60  thf('23', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 0.35/0.60      inference('sup-', [status(thm)], ['19', '22'])).
% 0.35/0.60  thf('24', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.35/0.60      inference('clc', [status(thm)], ['18', '23'])).
% 0.35/0.60  thf('25', plain,
% 0.35/0.60      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ X9 @ X12)
% 0.35/0.60          | ~ (r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X12)))),
% 0.35/0.60      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.35/0.60  thf('26', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.35/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.60  thf('27', plain,
% 0.35/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.35/0.60          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.35/0.60          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.35/0.60      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.35/0.60  thf('28', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.35/0.60          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.60  thf('29', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 0.35/0.60      inference('sup-', [status(thm)], ['3', '28'])).
% 0.35/0.60  thf('30', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.35/0.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.35/0.60  thf('31', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.35/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.60  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.35/0.60  
% 0.35/0.60  % SZS output end Refutation
% 0.35/0.60  
% 0.35/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
