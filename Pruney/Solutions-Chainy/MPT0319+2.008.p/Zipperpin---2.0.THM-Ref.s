%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8nOS4zpdWq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 117 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  443 (1470 expanded)
%              Number of equality atoms :   16 (  47 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
      | ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
      | ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X3 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X25 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( sk_A = X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( sk_A = X0 )
        | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ X0 ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( sk_A = sk_B )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('21',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['5','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('24',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X25 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( sk_A = X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8nOS4zpdWq
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 60 iterations in 0.036s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(l27_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k1_tarski @ X16) @ X17) | (r2_hidden @ X16 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.49  thf(t127_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.20/0.49       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ (k2_zfmisc_1 @ X20 @ X21))
% 0.20/0.49          | ~ (r1_xboole_0 @ X19 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((r2_hidden @ X1 @ X0)
% 0.20/0.49          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.20/0.49             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(t131_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( A ) != ( B ) ) =>
% 0.20/0.49       ( ( r1_xboole_0 @
% 0.20/0.49           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.20/0.49           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.20/0.49         ( r1_xboole_0 @
% 0.20/0.49           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.20/0.49           ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( ( A ) != ( B ) ) =>
% 0.20/0.49          ( ( r1_xboole_0 @
% 0.20/0.49              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.20/0.49              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.20/0.49            ( r1_xboole_0 @
% 0.20/0.49              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.20/0.49              ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t131_zfmisc_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))
% 0.20/0.49        | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.49             (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.49           (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B))))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B)))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k1_tarski @ X16) @ X17) | (r2_hidden @ X16 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ (k2_zfmisc_1 @ X20 @ X21))
% 0.20/0.49          | ~ (r1_xboole_0 @ X18 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((r2_hidden @ X1 @ X0)
% 0.20/0.49          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X3) @ 
% 0.20/0.49             (k2_zfmisc_1 @ X0 @ X2)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf(t64_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.49       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.20/0.49         ((r2_hidden @ X22 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X25)))
% 0.20/0.49          | ((X22) = (X25))
% 0.20/0.49          | ~ (r2_hidden @ X22 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((sk_A) = (X0))
% 0.20/0.49           | (r2_hidden @ sk_A @ 
% 0.20/0.49              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0)))))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(d5_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((![X0 : $i]: (((sk_A) = (X0)) | ~ (r2_hidden @ sk_A @ (k1_tarski @ X0))))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((((sk_A) = (sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '16'])).
% 0.20/0.49  thf('18', plain, (((sk_A) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B)))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['5', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.20/0.49         ((r2_hidden @ X22 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X25)))
% 0.20/0.49          | ((X22) = (X25))
% 0.20/0.49          | ~ (r2_hidden @ X22 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((sk_A) = (X0))
% 0.20/0.49           | (r2_hidden @ sk_A @ 
% 0.20/0.49              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0)))))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_D_1 @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_A) = (X0))
% 0.20/0.49          | (r2_hidden @ sk_A @ 
% 0.20/0.49             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0))))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]: (((sk_A) = (X0)) | ~ (r2_hidden @ sk_A @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, (((sk_A) = (sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '29'])).
% 0.20/0.49  thf('31', plain, (((sk_A) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('32', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
