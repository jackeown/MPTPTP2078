%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q8AzokgGNC

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:54 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   64 (  82 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  419 ( 676 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('18',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('20',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('30',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','37'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('40',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','5','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q8AzokgGNC
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 1.83/2.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.83/2.06  % Solved by: fo/fo7.sh
% 1.83/2.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.83/2.06  % done 1353 iterations in 1.613s
% 1.83/2.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.83/2.06  % SZS output start Refutation
% 1.83/2.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.83/2.06  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.83/2.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.83/2.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.83/2.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.83/2.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.83/2.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.83/2.06  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.83/2.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.83/2.06  thf(sk_B_type, type, sk_B: $i).
% 1.83/2.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.83/2.06  thf(sk_A_type, type, sk_A: $i).
% 1.83/2.06  thf(t41_subset_1, conjecture,
% 1.83/2.06    (![A:$i,B:$i]:
% 1.83/2.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.83/2.06       ( ![C:$i]:
% 1.83/2.06         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.83/2.06           ( r1_tarski @
% 1.83/2.06             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.83/2.06             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 1.83/2.06  thf(zf_stmt_0, negated_conjecture,
% 1.83/2.06    (~( ![A:$i,B:$i]:
% 1.83/2.06        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.83/2.06          ( ![C:$i]:
% 1.83/2.06            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.83/2.06              ( r1_tarski @
% 1.83/2.06                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.83/2.06                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 1.83/2.06    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 1.83/2.06  thf('0', plain,
% 1.83/2.06      (~ (r1_tarski @ 
% 1.83/2.06          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.83/2.06          (k3_subset_1 @ sk_A @ sk_B))),
% 1.83/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.06  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.83/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.06  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.83/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.06  thf(redefinition_k4_subset_1, axiom,
% 1.83/2.06    (![A:$i,B:$i,C:$i]:
% 1.83/2.06     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.83/2.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.83/2.06       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.83/2.06  thf('3', plain,
% 1.83/2.06      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.83/2.06         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 1.83/2.06          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 1.83/2.06          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 1.83/2.06      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.83/2.06  thf('4', plain,
% 1.83/2.06      (![X0 : $i]:
% 1.83/2.06         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 1.83/2.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.83/2.06      inference('sup-', [status(thm)], ['2', '3'])).
% 1.83/2.06  thf('5', plain,
% 1.83/2.06      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 1.83/2.06      inference('sup-', [status(thm)], ['1', '4'])).
% 1.83/2.06  thf('6', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.83/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.06  thf(d2_subset_1, axiom,
% 1.83/2.06    (![A:$i,B:$i]:
% 1.83/2.06     ( ( ( v1_xboole_0 @ A ) =>
% 1.83/2.06         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.83/2.06       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.83/2.06         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.83/2.06  thf('7', plain,
% 1.83/2.06      (![X15 : $i, X16 : $i]:
% 1.83/2.06         (~ (m1_subset_1 @ X15 @ X16)
% 1.83/2.06          | (r2_hidden @ X15 @ X16)
% 1.83/2.06          | (v1_xboole_0 @ X16))),
% 1.83/2.06      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.83/2.06  thf('8', plain,
% 1.83/2.06      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.83/2.06        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.83/2.06      inference('sup-', [status(thm)], ['6', '7'])).
% 1.83/2.06  thf(fc1_subset_1, axiom,
% 1.83/2.06    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.83/2.06  thf('9', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 1.83/2.06      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.83/2.06  thf('10', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.83/2.06      inference('clc', [status(thm)], ['8', '9'])).
% 1.83/2.06  thf(d1_zfmisc_1, axiom,
% 1.83/2.06    (![A:$i,B:$i]:
% 1.83/2.06     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.83/2.06       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.83/2.06  thf('11', plain,
% 1.83/2.06      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.83/2.06         (~ (r2_hidden @ X11 @ X10)
% 1.83/2.06          | (r1_tarski @ X11 @ X9)
% 1.83/2.06          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 1.83/2.06      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.83/2.06  thf('12', plain,
% 1.83/2.06      (![X9 : $i, X11 : $i]:
% 1.83/2.06         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 1.83/2.06      inference('simplify', [status(thm)], ['11'])).
% 1.83/2.06  thf('13', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 1.83/2.06      inference('sup-', [status(thm)], ['10', '12'])).
% 1.83/2.06  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.83/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.06  thf('15', plain,
% 1.83/2.06      (![X15 : $i, X16 : $i]:
% 1.83/2.06         (~ (m1_subset_1 @ X15 @ X16)
% 1.83/2.06          | (r2_hidden @ X15 @ X16)
% 1.83/2.06          | (v1_xboole_0 @ X16))),
% 1.83/2.06      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.83/2.06  thf('16', plain,
% 1.83/2.06      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.83/2.06        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.83/2.06      inference('sup-', [status(thm)], ['14', '15'])).
% 1.83/2.06  thf('17', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 1.83/2.06      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.83/2.06  thf('18', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.83/2.06      inference('clc', [status(thm)], ['16', '17'])).
% 1.83/2.06  thf('19', plain,
% 1.83/2.06      (![X9 : $i, X11 : $i]:
% 1.83/2.06         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 1.83/2.06      inference('simplify', [status(thm)], ['11'])).
% 1.83/2.06  thf('20', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.83/2.06      inference('sup-', [status(thm)], ['18', '19'])).
% 1.83/2.06  thf(t8_xboole_1, axiom,
% 1.83/2.06    (![A:$i,B:$i,C:$i]:
% 1.83/2.06     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.83/2.06       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.83/2.06  thf('21', plain,
% 1.83/2.06      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.83/2.06         (~ (r1_tarski @ X5 @ X6)
% 1.83/2.06          | ~ (r1_tarski @ X7 @ X6)
% 1.83/2.06          | (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 1.83/2.06      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.83/2.06  thf('22', plain,
% 1.83/2.06      (![X0 : $i]:
% 1.83/2.06         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 1.83/2.06          | ~ (r1_tarski @ X0 @ sk_A))),
% 1.83/2.06      inference('sup-', [status(thm)], ['20', '21'])).
% 1.83/2.06  thf('23', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 1.83/2.06      inference('sup-', [status(thm)], ['13', '22'])).
% 1.83/2.06  thf('24', plain,
% 1.83/2.06      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.83/2.06         (~ (r1_tarski @ X8 @ X9)
% 1.83/2.06          | (r2_hidden @ X8 @ X10)
% 1.83/2.06          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 1.83/2.06      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.83/2.06  thf('25', plain,
% 1.83/2.06      (![X8 : $i, X9 : $i]:
% 1.83/2.06         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 1.83/2.06      inference('simplify', [status(thm)], ['24'])).
% 1.83/2.06  thf('26', plain,
% 1.83/2.06      ((r2_hidden @ (k2_xboole_0 @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 1.83/2.06      inference('sup-', [status(thm)], ['23', '25'])).
% 1.83/2.06  thf('27', plain,
% 1.83/2.06      (![X15 : $i, X16 : $i]:
% 1.83/2.06         (~ (r2_hidden @ X15 @ X16)
% 1.83/2.06          | (m1_subset_1 @ X15 @ X16)
% 1.83/2.06          | (v1_xboole_0 @ X16))),
% 1.83/2.06      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.83/2.06  thf('28', plain,
% 1.83/2.06      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.83/2.06        | (m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 1.83/2.06      inference('sup-', [status(thm)], ['26', '27'])).
% 1.83/2.06  thf('29', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 1.83/2.06      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.83/2.06  thf('30', plain,
% 1.83/2.06      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 1.83/2.06      inference('clc', [status(thm)], ['28', '29'])).
% 1.83/2.06  thf(d5_subset_1, axiom,
% 1.83/2.06    (![A:$i,B:$i]:
% 1.83/2.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.83/2.06       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.83/2.06  thf('31', plain,
% 1.83/2.06      (![X18 : $i, X19 : $i]:
% 1.83/2.06         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 1.83/2.06          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 1.83/2.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.83/2.06  thf('32', plain,
% 1.83/2.06      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 1.83/2.06         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 1.83/2.06      inference('sup-', [status(thm)], ['30', '31'])).
% 1.83/2.06  thf('33', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.83/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.06  thf('34', plain,
% 1.83/2.06      (![X18 : $i, X19 : $i]:
% 1.83/2.06         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 1.83/2.06          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 1.83/2.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.83/2.06  thf('35', plain,
% 1.83/2.06      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.83/2.06      inference('sup-', [status(thm)], ['33', '34'])).
% 1.83/2.06  thf(t41_xboole_1, axiom,
% 1.83/2.06    (![A:$i,B:$i,C:$i]:
% 1.83/2.06     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.83/2.06       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.83/2.06  thf('36', plain,
% 1.83/2.06      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.83/2.06         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 1.83/2.06           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 1.83/2.06      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.83/2.06  thf('37', plain,
% 1.83/2.06      (![X0 : $i]:
% 1.83/2.06         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 1.83/2.06           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.83/2.06      inference('sup+', [status(thm)], ['35', '36'])).
% 1.83/2.06  thf('38', plain,
% 1.83/2.06      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 1.83/2.06         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 1.83/2.06      inference('demod', [status(thm)], ['32', '37'])).
% 1.83/2.06  thf(t36_xboole_1, axiom,
% 1.83/2.06    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.83/2.06  thf('39', plain,
% 1.83/2.06      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.83/2.06      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.83/2.06  thf('40', plain,
% 1.83/2.06      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)) @ 
% 1.83/2.06        (k3_subset_1 @ sk_A @ sk_B))),
% 1.83/2.06      inference('sup+', [status(thm)], ['38', '39'])).
% 1.83/2.06  thf('41', plain, ($false),
% 1.83/2.06      inference('demod', [status(thm)], ['0', '5', '40'])).
% 1.83/2.06  
% 1.83/2.06  % SZS output end Refutation
% 1.83/2.06  
% 1.83/2.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
