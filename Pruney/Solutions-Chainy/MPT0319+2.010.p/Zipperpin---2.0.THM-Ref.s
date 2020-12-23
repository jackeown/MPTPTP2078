%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lH2oKzRVqZ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:31 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   45 (  65 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  414 ( 715 expanded)
%              Number of equality atoms :   38 (  58 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) )
      | ( X14 = X15 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X10 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( X1 = X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X1 = X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t131_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( A != B )
     => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
        & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( A != B )
       => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
          & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_zfmisc_1])).

thf('11',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( X3 = X2 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X3 = X2 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) )
      | ( X3 = X2 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['11'])).

thf('21',plain,
    ( ( sk_A = sk_B )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['11'])).

thf('25',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['12','25'])).

thf('27',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['10','26'])).

thf('28',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lH2oKzRVqZ
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:01:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.72/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.90  % Solved by: fo/fo7.sh
% 0.72/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.90  % done 144 iterations in 0.455s
% 0.72/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.90  % SZS output start Refutation
% 0.72/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.72/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.72/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.90  thf(t17_zfmisc_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ( A ) != ( B ) ) =>
% 0.72/0.90       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.72/0.90  thf('0', plain,
% 0.72/0.90      (![X14 : $i, X15 : $i]:
% 0.72/0.90         ((r1_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15))
% 0.72/0.90          | ((X14) = (X15)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.72/0.90  thf(d7_xboole_0, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.72/0.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.72/0.90  thf('1', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.90  thf('2', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (((X1) = (X0))
% 0.72/0.90          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.72/0.90              = (k1_xboole_0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['0', '1'])).
% 0.72/0.90  thf(t123_zfmisc_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.90     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.72/0.90       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.72/0.90  thf('3', plain,
% 0.72/0.90      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.72/0.90         ((k2_zfmisc_1 @ (k3_xboole_0 @ X10 @ X12) @ (k3_xboole_0 @ X11 @ X13))
% 0.72/0.90           = (k3_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 0.72/0.90              (k2_zfmisc_1 @ X12 @ X13)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.72/0.90  thf('4', plain,
% 0.72/0.90      (![X0 : $i, X2 : $i]:
% 0.72/0.90         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.72/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.90  thf('5', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.90         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.72/0.90            != (k1_xboole_0))
% 0.72/0.90          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['3', '4'])).
% 0.72/0.90  thf('6', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.90         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ k1_xboole_0)
% 0.72/0.90            != (k1_xboole_0))
% 0.72/0.90          | ((X1) = (X0))
% 0.72/0.90          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.72/0.90             (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['2', '5'])).
% 0.72/0.90  thf(t113_zfmisc_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.72/0.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.72/0.90  thf('7', plain,
% 0.72/0.90      (![X6 : $i, X7 : $i]:
% 0.72/0.90         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.72/0.90  thf('8', plain,
% 0.72/0.90      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['7'])).
% 0.72/0.90  thf('9', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.90         (((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.90          | ((X1) = (X0))
% 0.72/0.90          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.72/0.90             (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0))))),
% 0.72/0.90      inference('demod', [status(thm)], ['6', '8'])).
% 0.72/0.90  thf('10', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.90         ((r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.72/0.90           (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((X1) = (X0)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['9'])).
% 0.72/0.90  thf(t131_zfmisc_1, conjecture,
% 0.72/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.90     ( ( ( A ) != ( B ) ) =>
% 0.72/0.90       ( ( r1_xboole_0 @
% 0.72/0.90           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.72/0.90           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.72/0.90         ( r1_xboole_0 @
% 0.72/0.90           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.72/0.90           ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ))).
% 0.72/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.90        ( ( ( A ) != ( B ) ) =>
% 0.72/0.90          ( ( r1_xboole_0 @
% 0.72/0.90              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.72/0.90              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.72/0.90            ( r1_xboole_0 @
% 0.72/0.90              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.72/0.90              ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )),
% 0.72/0.90    inference('cnf.neg', [status(esa)], [t131_zfmisc_1])).
% 0.72/0.90  thf('11', plain,
% 0.72/0.90      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.72/0.90           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))
% 0.72/0.90        | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.72/0.90             (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('12', plain,
% 0.72/0.90      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.72/0.90           (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))
% 0.72/0.90         <= (~
% 0.72/0.90             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.72/0.90               (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))))),
% 0.72/0.90      inference('split', [status(esa)], ['11'])).
% 0.72/0.90  thf('13', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (((X1) = (X0))
% 0.72/0.90          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.72/0.90              = (k1_xboole_0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['0', '1'])).
% 0.72/0.90  thf('14', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.90         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.72/0.90            != (k1_xboole_0))
% 0.72/0.90          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['3', '4'])).
% 0.72/0.90  thf('15', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.90         (((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.72/0.90            != (k1_xboole_0))
% 0.72/0.90          | ((X3) = (X2))
% 0.72/0.90          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X3) @ X1) @ 
% 0.72/0.90             (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['13', '14'])).
% 0.72/0.90  thf('16', plain,
% 0.72/0.90      (![X6 : $i, X7 : $i]:
% 0.72/0.90         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.72/0.90  thf('17', plain,
% 0.72/0.90      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['16'])).
% 0.72/0.90  thf('18', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.90         (((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.90          | ((X3) = (X2))
% 0.72/0.90          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X3) @ X1) @ 
% 0.72/0.90             (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['15', '17'])).
% 0.72/0.90  thf('19', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.90         ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X3) @ X1) @ 
% 0.72/0.90           (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0))
% 0.72/0.90          | ((X3) = (X2)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['18'])).
% 0.72/0.90  thf('20', plain,
% 0.72/0.90      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.72/0.90           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))
% 0.72/0.90         <= (~
% 0.72/0.90             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.72/0.90               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.72/0.90      inference('split', [status(esa)], ['11'])).
% 0.72/0.90  thf('21', plain,
% 0.72/0.90      ((((sk_A) = (sk_B)))
% 0.72/0.90         <= (~
% 0.72/0.90             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.72/0.90               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['19', '20'])).
% 0.72/0.90  thf('22', plain, (((sk_A) != (sk_B))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('23', plain,
% 0.72/0.90      (((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.72/0.90         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.72/0.90  thf('24', plain,
% 0.72/0.90      (~
% 0.72/0.90       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.72/0.90         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))) | 
% 0.72/0.90       ~
% 0.72/0.90       ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.72/0.90         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.72/0.90      inference('split', [status(esa)], ['11'])).
% 0.72/0.90  thf('25', plain,
% 0.72/0.90      (~
% 0.72/0.90       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.72/0.90         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.72/0.90      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.72/0.90  thf('26', plain,
% 0.72/0.90      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.72/0.90          (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))),
% 0.72/0.90      inference('simpl_trail', [status(thm)], ['12', '25'])).
% 0.72/0.90  thf('27', plain, (((sk_A) = (sk_B))),
% 0.72/0.90      inference('sup-', [status(thm)], ['10', '26'])).
% 0.72/0.90  thf('28', plain, (((sk_A) != (sk_B))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('29', plain, ($false),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.72/0.90  
% 0.72/0.90  % SZS output end Refutation
% 0.72/0.90  
% 0.72/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
