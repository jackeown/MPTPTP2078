%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4dQ9dTQQZL

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  64 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  338 ( 676 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t33_finset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( v1_finset_1 @ A )
          & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ! [D: $i] :
              ~ ( ( v1_finset_1 @ D )
                & ( r1_tarski @ D @ B )
                & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_finset_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_finset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( v1_finset_1 @ E )
              & ( r1_tarski @ E @ C )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_finset_1 @ X8 )
      | ( r1_tarski @ ( sk_E @ X9 @ X10 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('2',plain,
    ( ( r1_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(demod,[status(thm)],['2','3'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X5 ) @ ( k2_zfmisc_1 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_finset_1 @ X8 )
      | ( r1_tarski @ X8 @ ( k2_zfmisc_1 @ ( sk_D @ X9 @ X10 @ X8 ) @ ( sk_E @ X9 @ X10 @ X8 ) ) )
      | ~ ( r1_tarski @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('9',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X11: $i] :
      ( ~ ( v1_finset_1 @ X11 )
      | ~ ( r1_tarski @ X11 @ sk_B )
      | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ X11 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_finset_1 @ X8 )
      | ( r1_tarski @ ( sk_D @ X9 @ X10 @ X8 ) @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('21',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_finset_1 @ X8 )
      | ( v1_finset_1 @ ( sk_D @ X9 @ X10 @ X8 ) )
      | ~ ( r1_tarski @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('26',plain,
    ( ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['18','23','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4dQ9dTQQZL
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 147 iterations in 0.125s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.58  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(t33_finset_1, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.58          ( ![D:$i]:
% 0.20/0.58            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.20/0.58                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.58        ( ~( ( v1_finset_1 @ A ) & 
% 0.20/0.58             ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.58             ( ![D:$i]:
% 0.20/0.58               ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.20/0.58                    ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t33_finset_1])).
% 0.20/0.58  thf('0', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t32_finset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.58          ( ![D:$i,E:$i]:
% 0.20/0.58            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.20/0.58                 ( v1_finset_1 @ E ) & ( r1_tarski @ E @ C ) & 
% 0.20/0.58                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) ) ) ))).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.58         (~ (v1_finset_1 @ X8)
% 0.20/0.58          | (r1_tarski @ (sk_E @ X9 @ X10 @ X8) @ X9)
% 0.20/0.58          | ~ (r1_tarski @ X8 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (((r1_tarski @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.58        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.58  thf('3', plain, ((v1_finset_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('4', plain, ((r1_tarski @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.20/0.58      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.58  thf(t118_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.58       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.58         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.58         (~ (r1_tarski @ X5 @ X6)
% 0.20/0.58          | (r1_tarski @ (k2_zfmisc_1 @ X7 @ X5) @ (k2_zfmisc_1 @ X7 @ X6)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.58          (k2_zfmisc_1 @ X0 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.58  thf('7', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.58         (~ (v1_finset_1 @ X8)
% 0.20/0.58          | (r1_tarski @ X8 @ 
% 0.20/0.58             (k2_zfmisc_1 @ (sk_D @ X9 @ X10 @ X8) @ (sk_E @ X9 @ X10 @ X8)))
% 0.20/0.58          | ~ (r1_tarski @ X8 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (((r1_tarski @ sk_A @ 
% 0.20/0.58         (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.58          (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.20/0.58        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.58  thf('10', plain, ((v1_finset_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      ((r1_tarski @ sk_A @ 
% 0.20/0.58        (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.58         (sk_E @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.58  thf(t12_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i]:
% 0.20/0.58         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (((k2_xboole_0 @ sk_A @ 
% 0.20/0.58         (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.58          (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.20/0.58         = (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.58            (sk_E @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.58  thf(t11_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_tarski @ 
% 0.20/0.58             (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.58              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.58             X0)
% 0.20/0.58          | (r1_tarski @ sk_A @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['6', '15'])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      (![X11 : $i]:
% 0.20/0.58         (~ (v1_finset_1 @ X11)
% 0.20/0.58          | ~ (r1_tarski @ X11 @ sk_B)
% 0.20/0.58          | ~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ X11 @ sk_C)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      ((~ (r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.58        | ~ (v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.58  thf('19', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.58         (~ (v1_finset_1 @ X8)
% 0.20/0.58          | (r1_tarski @ (sk_D @ X9 @ X10 @ X8) @ X10)
% 0.20/0.58          | ~ (r1_tarski @ X8 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (((r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.58        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('22', plain, ((v1_finset_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('23', plain, ((r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.58  thf('24', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.58         (~ (v1_finset_1 @ X8)
% 0.20/0.58          | (v1_finset_1 @ (sk_D @ X9 @ X10 @ X8))
% 0.20/0.58          | ~ (r1_tarski @ X8 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A)) | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.58  thf('27', plain, ((v1_finset_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('28', plain, ((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A))),
% 0.20/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.58  thf('29', plain, ($false),
% 0.20/0.58      inference('demod', [status(thm)], ['18', '23', '28'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
