%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zcJluz6eM8

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 116 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  426 ( 804 expanded)
%              Number of equality atoms :   18 (  37 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X30: $i] :
      ( r1_tarski @ X30 @ ( k1_zfmisc_1 @ ( k3_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k2_tarski @ X32 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
      | ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t12_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_mcart_1])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ X36 @ X37 )
      | ~ ( r2_hidden @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('25',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['21'])).

thf('27',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['21'])).

thf('29',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['22','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['20','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
      | ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k2_tarski @ X32 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('41',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ X36 @ X37 )
      | ~ ( r2_hidden @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('47',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['31','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zcJluz6eM8
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 98 iterations in 0.037s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('0', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf(t31_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.49  thf('1', plain, (![X31 : $i]: ((k3_tarski @ (k1_tarski @ X31)) = (X31))),
% 0.21/0.49      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.21/0.49  thf('2', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t100_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X30 : $i]: (r1_tarski @ X30 @ (k1_zfmisc_1 @ (k3_tarski @ X30)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i]: (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(t38_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.49         ((r2_hidden @ X32 @ X33)
% 0.21/0.49          | ~ (r1_tarski @ (k2_tarski @ X32 @ X34) @ X33))),
% 0.21/0.49      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.49  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(l27_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X28 : $i, X29 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k1_tarski @ X28) @ X29) | (r2_hidden @ X28 @ X29))),
% 0.21/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.49  thf(t12_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.49       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.49         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.49          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.49            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t12_mcart_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t10_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.49       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.49         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.49         ((r2_hidden @ (k1_mcart_1 @ X41) @ X42)
% 0.21/0.49          | ~ (r2_hidden @ X41 @ (k2_zfmisc_1 @ X42 @ X43)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.49  thf('10', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(t3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.49          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.21/0.49          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.49  thf('14', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '13'])).
% 0.21/0.49  thf(t1_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X36 : $i, X37 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X36 @ X37) | ~ (r2_hidden @ X36 @ X37))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X38 : $i, X39 : $i]:
% 0.21/0.49         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('18', plain, ((r1_tarski @ sk_B @ (k1_mcart_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X4 : $i, X6 : $i]:
% 0.21/0.49         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((~ (r1_tarski @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.21/0.49        | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.21/0.49        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.49         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.49         ((r2_hidden @ (k2_mcart_1 @ X41) @ X43)
% 0.21/0.49          | ~ (r2_hidden @ X41 @ (k2_zfmisc_1 @ X42 @ X43)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.49  thf('25', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))
% 0.21/0.49         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('27', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.21/0.49       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('29', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['22', '29'])).
% 0.21/0.49  thf('31', plain, (~ (r1_tarski @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['20', '30'])).
% 0.21/0.49  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X28 : $i, X29 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k1_tarski @ X28) @ X29) | (r2_hidden @ X28 @ X29))),
% 0.21/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('35', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.49  thf('36', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.49         ((r2_hidden @ X32 @ X33)
% 0.21/0.49          | ~ (r1_tarski @ (k2_tarski @ X32 @ X34) @ X33))),
% 0.21/0.49      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.49  thf('41', plain, ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.49          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k1_tarski @ (k1_mcart_1 @ sk_A)) @ X0)
% 0.21/0.49          | ~ (r2_hidden @ sk_B @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '43'])).
% 0.21/0.49  thf('45', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X36 : $i, X37 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X36 @ X37) | ~ (r2_hidden @ X36 @ X37))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((m1_subset_1 @ (k1_mcart_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X38 : $i, X39 : $i]:
% 0.21/0.49         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('49', plain, ((r1_tarski @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain, ($false), inference('demod', [status(thm)], ['31', '49'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
