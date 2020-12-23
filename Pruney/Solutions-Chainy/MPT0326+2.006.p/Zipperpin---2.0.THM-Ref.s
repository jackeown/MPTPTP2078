%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p9Wc22EZMp

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 122 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  475 (1056 expanded)
%              Number of equality atoms :   35 (  54 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_2 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_zfmisc_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X19 @ X20 ) )
      | ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('5',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_D )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( ( r1_xboole_0 @ X12 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('18',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference(demod,[status(thm)],['16','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','23'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_2 ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf('31',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['2','31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_zfmisc_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X19 @ X20 ) )
      | ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('34',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_zfmisc_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','23'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p9Wc22EZMp
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:34:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 66 iterations in 0.045s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(t139_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50       ( ![B:$i,C:$i,D:$i]:
% 0.20/0.50         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.20/0.50             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.20/0.50           ( r1_tarski @ B @ D ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50          ( ![B:$i,C:$i,D:$i]:
% 0.20/0.50            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.20/0.50                ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.20/0.50              ( r1_tarski @ B @ D ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t139_zfmisc_1])).
% 0.20/0.50  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 0.20/0.50        | (r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.50           (k2_zfmisc_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_D @ sk_C_2)))
% 0.20/0.50         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_D @ sk_C_2))))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C_2 @ sk_D)))
% 0.20/0.50         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C_2 @ sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf(t138_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.20/0.50       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X17 @ X18) = (k1_xboole_0))
% 0.20/0.50          | ~ (r1_tarski @ (k2_zfmisc_1 @ X17 @ X18) @ 
% 0.20/0.50               (k2_zfmisc_1 @ X19 @ X20))
% 0.20/0.50          | (r1_tarski @ X18 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((((r1_tarski @ sk_B_1 @ sk_D)
% 0.20/0.50         | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.20/0.50         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C_2 @ sk_D))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.50         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C_2 @ sk_D))))),
% 0.20/0.50      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf(t113_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (((X14) = (k1_xboole_0))
% 0.20/0.50          | ((X15) = (k1_xboole_0))
% 0.20/0.50          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1) = (k1_xboole_0))))
% 0.20/0.50         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C_2 @ sk_D))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C_2 @ sk_D))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i]:
% 0.20/0.50         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C_2 @ sk_D))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.50  thf(t66_xboole_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X12 : $i]: ((r1_xboole_0 @ X12 @ X12) | ((X12) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.50  thf('18', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.50  thf('20', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.50  thf(t4_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.20/0.50          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.50  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C_2 @ sk_D))))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '24'])).
% 0.20/0.50  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.20/0.50         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C_2 @ sk_D))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (~
% 0.20/0.50       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_D @ sk_C_2))) | 
% 0.20/0.50       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.50        (k2_zfmisc_1 @ sk_D @ sk_C_2))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['2', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X17 @ X18) = (k1_xboole_0))
% 0.20/0.50          | ~ (r1_tarski @ (k2_zfmisc_1 @ X17 @ X18) @ 
% 0.20/0.50               (k2_zfmisc_1 @ X19 @ X20))
% 0.20/0.50          | (r1_tarski @ X17 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((r1_tarski @ sk_B_1 @ sk_D)
% 0.20/0.50        | ((k2_zfmisc_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain, (((k2_zfmisc_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (((X14) = (k1_xboole_0))
% 0.20/0.50          | ((X15) = (k1_xboole_0))
% 0.20/0.50          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.50  thf('40', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      ((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i]:
% 0.20/0.50         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['42', '45'])).
% 0.20/0.50  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['41', '46'])).
% 0.20/0.50  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.50  thf('49', plain, ($false),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '47', '48'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
