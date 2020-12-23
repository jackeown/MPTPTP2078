%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DgLjpJwGwn

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 126 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  455 ( 924 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ( r2_hidden @ X25 @ X26 ) ) ),
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

thf('6',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('8',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    r1_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['19'])).

thf('25',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['19'])).

thf('27',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['20','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['18','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('31',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('32',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('33',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ ( k1_tarski @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('40',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_B )
    = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('47',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','49'])).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('52',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['29','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DgLjpJwGwn
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:41:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 133 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.50  thf(d1_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X17 @ X18)
% 0.21/0.50          | (r2_hidden @ X17 @ X19)
% 0.21/0.50          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((r2_hidden @ X17 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X17 @ X18))),
% 0.21/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.50  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.50  thf(l27_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X25 : $i, X26 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k1_tarski @ X25) @ X26) | (r2_hidden @ X25 @ X26))),
% 0.21/0.50      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.50  thf(t12_mcart_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.50       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.50          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.50            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t12_mcart_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_2))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t10_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_mcart_1 @ X32) @ X33)
% 0.21/0.50          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('8', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(t3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.50  thf('12', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '11'])).
% 0.21/0.50  thf(t1_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X27 : $i, X28 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X29 : $i, X30 : $i]:
% 0.21/0.50         ((r1_tarski @ X29 @ X30) | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('16', plain, ((r1_tarski @ sk_B @ (k1_mcart_1 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X4 : $i, X6 : $i]:
% 0.21/0.50         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.21/0.50        | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.21/0.50        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.50         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_2))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.50         ((r2_hidden @ (k2_mcart_1 @ X32) @ X34)
% 0.21/0.50          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('23', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2)),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))
% 0.21/0.50         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2)))),
% 0.21/0.50      inference('split', [status(esa)], ['19'])).
% 0.21/0.50  thf('25', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.21/0.50       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))),
% 0.21/0.50      inference('split', [status(esa)], ['19'])).
% 0.21/0.50  thf('27', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['20', '27'])).
% 0.21/0.50  thf('29', plain, (~ (r1_tarski @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['18', '28'])).
% 0.21/0.50  thf('30', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.50  thf('31', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(l1_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X22 : $i, X24 : $i]:
% 0.21/0.50         ((r1_tarski @ (k1_tarski @ X22) @ X24) | ~ (r2_hidden @ X22 @ X24))),
% 0.21/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((r1_tarski @ (k1_tarski @ (k1_mcart_1 @ sk_A)) @ (k1_tarski @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X4 : $i, X6 : $i]:
% 0.21/0.50         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.21/0.50        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i]:
% 0.21/0.50         ((r2_hidden @ X22 @ X23) | ~ (r1_tarski @ (k1_tarski @ X22) @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.50  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.50  thf('40', plain, ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X22 : $i, X24 : $i]:
% 0.21/0.50         ((r1_tarski @ (k1_tarski @ X22) @ X24) | ~ (r2_hidden @ X22 @ X24))),
% 0.21/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, (((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X25 : $i, X26 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k1_tarski @ X25) @ X26) | (r2_hidden @ X25 @ X26))),
% 0.21/0.50      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.21/0.50          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['45', '48'])).
% 0.21/0.50  thf('50', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X27 : $i, X28 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((m1_subset_1 @ (k1_mcart_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X29 : $i, X30 : $i]:
% 0.21/0.50         ((r1_tarski @ X29 @ X30) | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('54', plain, ((r1_tarski @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain, ($false), inference('demod', [status(thm)], ['29', '54'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
