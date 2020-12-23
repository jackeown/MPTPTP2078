%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLoc442ipP

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:14 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   67 (  96 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  502 ( 796 expanded)
%              Number of equality atoms :   50 (  79 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t124_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
        = ( k2_zfmisc_1 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
          = ( k2_zfmisc_1 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['14','22'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('24',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X35 @ X37 ) @ ( k3_xboole_0 @ X36 @ X38 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k3_xboole_0 @ X0 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_C_1 ) )
    | ( sk_C_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C_1 )
 != ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','25','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLoc442ipP
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:57:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.91/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.15  % Solved by: fo/fo7.sh
% 0.91/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.15  % done 1132 iterations in 0.709s
% 0.91/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.15  % SZS output start Refutation
% 0.91/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.15  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.15  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.91/1.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.91/1.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.15  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.91/1.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(t124_zfmisc_1, conjecture,
% 0.91/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.15     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.91/1.15       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.91/1.15         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.91/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.15    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.15        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.91/1.15          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.91/1.15            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.91/1.15    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.91/1.15  thf('0', plain,
% 0.91/1.15      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D_1) @ 
% 0.91/1.15         (k2_zfmisc_1 @ sk_B @ sk_C_1)) != (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(t12_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.15  thf('2', plain,
% 0.91/1.15      (![X14 : $i, X15 : $i]:
% 0.91/1.15         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.91/1.15      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.15  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.91/1.15      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.15  thf(t95_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k3_xboole_0 @ A @ B ) =
% 0.91/1.15       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.91/1.15  thf('4', plain,
% 0.91/1.15      (![X22 : $i, X23 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X22 @ X23)
% 0.91/1.15           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.91/1.15              (k2_xboole_0 @ X22 @ X23)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.91/1.15  thf(t91_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.15       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.91/1.15  thf('5', plain,
% 0.91/1.15      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.91/1.15         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.91/1.15           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.15  thf('6', plain,
% 0.91/1.15      (![X22 : $i, X23 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X22 @ X23)
% 0.91/1.15           = (k5_xboole_0 @ X22 @ 
% 0.91/1.15              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.91/1.16      inference('demod', [status(thm)], ['4', '5'])).
% 0.91/1.16  thf('7', plain,
% 0.91/1.16      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.91/1.16         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.91/1.16      inference('sup+', [status(thm)], ['3', '6'])).
% 0.91/1.16  thf(idempotence_k3_xboole_0, axiom,
% 0.91/1.16    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.91/1.16  thf('8', plain, (![X11 : $i]: ((k3_xboole_0 @ X11 @ X11) = (X11))),
% 0.91/1.16      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.91/1.16  thf(t100_xboole_1, axiom,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.16  thf('9', plain,
% 0.91/1.16      (![X12 : $i, X13 : $i]:
% 0.91/1.16         ((k4_xboole_0 @ X12 @ X13)
% 0.91/1.16           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.91/1.16      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.16  thf('10', plain,
% 0.91/1.16      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.16      inference('sup+', [status(thm)], ['8', '9'])).
% 0.91/1.16  thf('11', plain,
% 0.91/1.16      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.16      inference('sup+', [status(thm)], ['8', '9'])).
% 0.91/1.16  thf(t92_xboole_1, axiom,
% 0.91/1.16    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.91/1.16  thf('12', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.91/1.16      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.16  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.16      inference('sup+', [status(thm)], ['11', '12'])).
% 0.91/1.16  thf('14', plain,
% 0.91/1.16      (((k3_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.91/1.16      inference('demod', [status(thm)], ['7', '10', '13'])).
% 0.91/1.16  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.16      inference('sup+', [status(thm)], ['11', '12'])).
% 0.91/1.16  thf(idempotence_k2_xboole_0, axiom,
% 0.91/1.16    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.91/1.16  thf('16', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ X10) = (X10))),
% 0.91/1.16      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.91/1.16  thf('17', plain,
% 0.91/1.16      (![X22 : $i, X23 : $i]:
% 0.91/1.16         ((k3_xboole_0 @ X22 @ X23)
% 0.91/1.16           = (k5_xboole_0 @ X22 @ 
% 0.91/1.16              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.91/1.16      inference('demod', [status(thm)], ['4', '5'])).
% 0.91/1.16  thf('18', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         ((k3_xboole_0 @ X0 @ X0)
% 0.91/1.16           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.91/1.16      inference('sup+', [status(thm)], ['16', '17'])).
% 0.91/1.16  thf('19', plain, (![X11 : $i]: ((k3_xboole_0 @ X11 @ X11) = (X11))),
% 0.91/1.16      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.91/1.16  thf('20', plain,
% 0.91/1.16      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.16      inference('sup+', [status(thm)], ['8', '9'])).
% 0.91/1.16  thf('21', plain,
% 0.91/1.16      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.91/1.16      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.91/1.16  thf('22', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.16      inference('sup+', [status(thm)], ['15', '21'])).
% 0.91/1.16  thf('23', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.91/1.16      inference('demod', [status(thm)], ['14', '22'])).
% 0.91/1.16  thf(t123_zfmisc_1, axiom,
% 0.91/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.16     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.91/1.16       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.91/1.16  thf('24', plain,
% 0.91/1.16      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.91/1.16         ((k2_zfmisc_1 @ (k3_xboole_0 @ X35 @ X37) @ (k3_xboole_0 @ X36 @ X38))
% 0.91/1.16           = (k3_xboole_0 @ (k2_zfmisc_1 @ X35 @ X36) @ 
% 0.91/1.16              (k2_zfmisc_1 @ X37 @ X38)))),
% 0.91/1.16      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.91/1.16  thf('25', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.91/1.16              (k2_zfmisc_1 @ sk_B @ X0)))),
% 0.91/1.16      inference('sup+', [status(thm)], ['23', '24'])).
% 0.91/1.16  thf(d4_xboole_0, axiom,
% 0.91/1.16    (![A:$i,B:$i,C:$i]:
% 0.91/1.16     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.91/1.16       ( ![D:$i]:
% 0.91/1.16         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.16           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.91/1.16  thf('26', plain,
% 0.91/1.16      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.91/1.16         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.91/1.16          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.91/1.16          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('27', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['26'])).
% 0.91/1.16  thf('28', plain, ((r1_tarski @ sk_C_1 @ sk_D_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf(d3_tarski, axiom,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( r1_tarski @ A @ B ) <=>
% 0.91/1.16       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.91/1.16  thf('29', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ X1)
% 0.91/1.16          | (r2_hidden @ X0 @ X2)
% 0.91/1.16          | ~ (r1_tarski @ X1 @ X2))),
% 0.91/1.16      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.16  thf('30', plain,
% 0.91/1.16      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['28', '29'])).
% 0.91/1.16  thf('31', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((sk_C_1) = (k3_xboole_0 @ X0 @ sk_C_1))
% 0.91/1.16          | (r2_hidden @ (sk_D @ sk_C_1 @ sk_C_1 @ X0) @ sk_D_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['27', '30'])).
% 0.91/1.16  thf('32', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['26'])).
% 0.91/1.16  thf('33', plain,
% 0.91/1.16      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.91/1.16         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('34', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['32', '33'])).
% 0.91/1.16  thf('35', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['34'])).
% 0.91/1.16  thf('36', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['26'])).
% 0.91/1.16  thf('37', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.91/1.16      inference('clc', [status(thm)], ['35', '36'])).
% 0.91/1.16  thf('38', plain,
% 0.91/1.16      ((((sk_C_1) = (k3_xboole_0 @ sk_D_1 @ sk_C_1))
% 0.91/1.16        | ((sk_C_1) = (k3_xboole_0 @ sk_D_1 @ sk_C_1)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['31', '37'])).
% 0.91/1.16  thf('39', plain, (((sk_C_1) = (k3_xboole_0 @ sk_D_1 @ sk_C_1))),
% 0.91/1.16      inference('simplify', [status(thm)], ['38'])).
% 0.91/1.16  thf('40', plain,
% 0.91/1.16      (((k2_zfmisc_1 @ sk_A @ sk_C_1) != (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.91/1.16      inference('demod', [status(thm)], ['0', '25', '39'])).
% 0.91/1.16  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.91/1.16  
% 0.91/1.16  % SZS output end Refutation
% 0.91/1.16  
% 0.91/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
