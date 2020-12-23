%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.adjv8hzE1Y

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:26 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  188 ( 219 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t63_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_subset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X22 ) @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( k2_subset_1 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X16 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('12',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( m1_subset_1 @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ X18 @ X19 )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.adjv8hzE1Y
% 0.14/0.36  % Computer   : n018.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:21:12 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 80 iterations in 0.032s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(t63_subset_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.23/0.51       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i]:
% 0.23/0.51        ( ( r2_hidden @ A @ B ) =>
% 0.23/0.51          ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t63_subset_1])).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(dt_k2_subset_1, axiom,
% 0.23/0.51    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X22 : $i]: (m1_subset_1 @ (k2_subset_1 @ X22) @ (k1_zfmisc_1 @ X22))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.23/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.51  thf('2', plain, (![X21 : $i]: ((k2_subset_1 @ X21) = (X21))),
% 0.23/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.51  thf('3', plain, (![X22 : $i]: (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X22))),
% 0.23/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf(d2_subset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X18 : $i, X19 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X18 @ X19)
% 0.23/0.51          | (r2_hidden @ X18 @ X19)
% 0.23/0.51          | (v1_xboole_0 @ X19))),
% 0.23/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.23/0.51          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(fc1_subset_1, axiom,
% 0.23/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.51  thf('6', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.23/0.51  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.23/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf('8', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(l1_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X13 : $i, X15 : $i]:
% 0.23/0.51         ((r1_tarski @ (k1_tarski @ X13) @ X15) | ~ (r2_hidden @ X13 @ X15))),
% 0.23/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.23/0.51  thf('10', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.23/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.51  thf(t79_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.23/0.51       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X16 : $i, X17 : $i]:
% 0.23/0.51         ((r1_tarski @ (k1_zfmisc_1 @ X16) @ (k1_zfmisc_1 @ X17))
% 0.23/0.51          | ~ (r1_tarski @ X16 @ X17))),
% 0.23/0.51      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      ((r1_tarski @ (k1_zfmisc_1 @ (k1_tarski @ sk_A)) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.51  thf(d3_tarski, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.23/0.51          | (r2_hidden @ X3 @ X5)
% 0.23/0.51          | ~ (r1_tarski @ X4 @ X5))),
% 0.23/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.23/0.51          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k1_tarski @ sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.51  thf('15', plain, ((r2_hidden @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['7', '14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X18 : $i, X19 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X18 @ X19)
% 0.23/0.51          | (m1_subset_1 @ X18 @ X19)
% 0.23/0.51          | (v1_xboole_0 @ X19))),
% 0.23/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.51  thf(d1_xboole_0, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X18 : $i, X19 : $i]:
% 0.23/0.51         ((m1_subset_1 @ X18 @ X19) | ~ (r2_hidden @ X18 @ X19))),
% 0.23/0.51      inference('clc', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      ((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.23/0.51  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.35/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
