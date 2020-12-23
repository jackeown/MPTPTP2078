%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OAEFgrOfvw

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:06 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   53 (  60 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  306 ( 371 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X47: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X47 ) @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X46: $i] :
      ( ( k2_subset_1 @ X46 )
      = X46 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X47: $i] :
      ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X50 ) )
      | ( ( k4_subset_1 @ X50 @ X49 @ X51 )
        = ( k2_xboole_0 @ X49 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ X44 )
      | ( r2_hidden @ X43 @ X44 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X48: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ( r2_hidden @ X35 @ X36 )
      | ( X36
       != ( k3_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('14',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X35 @ ( k3_tarski @ X34 ) )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X42: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['20'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','23'])).

thf('25',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X46: $i] :
      ( ( k2_subset_1 @ X46 )
      = X46 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ! [X46: $i] :
      ( ( k2_subset_1 @ X46 )
      = X46 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OAEFgrOfvw
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.53  % Solved by: fo/fo7.sh
% 0.33/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.53  % done 126 iterations in 0.071s
% 0.33/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.53  % SZS output start Refutation
% 0.33/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.33/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.33/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.33/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.33/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.33/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.53  thf(dt_k2_subset_1, axiom,
% 0.33/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.33/0.53  thf('0', plain,
% 0.33/0.53      (![X47 : $i]: (m1_subset_1 @ (k2_subset_1 @ X47) @ (k1_zfmisc_1 @ X47))),
% 0.33/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.33/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.33/0.53  thf('1', plain, (![X46 : $i]: ((k2_subset_1 @ X46) = (X46))),
% 0.33/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.33/0.53  thf('2', plain, (![X47 : $i]: (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X47))),
% 0.33/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.33/0.53  thf(t28_subset_1, conjecture,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.53       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.33/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.53    (~( ![A:$i,B:$i]:
% 0.33/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.53          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.33/0.53    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.33/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(redefinition_k4_subset_1, axiom,
% 0.33/0.53    (![A:$i,B:$i,C:$i]:
% 0.33/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.33/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.53       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.33/0.53  thf('4', plain,
% 0.33/0.53      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 0.33/0.53          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X50))
% 0.33/0.53          | ((k4_subset_1 @ X50 @ X49 @ X51) = (k2_xboole_0 @ X49 @ X51)))),
% 0.33/0.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.33/0.53  thf('5', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.33/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.33/0.53  thf('6', plain,
% 0.33/0.53      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['2', '5'])).
% 0.33/0.53  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(d2_subset_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.33/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.33/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.33/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.33/0.53  thf('8', plain,
% 0.33/0.53      (![X43 : $i, X44 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X43 @ X44)
% 0.33/0.53          | (r2_hidden @ X43 @ X44)
% 0.33/0.53          | (v1_xboole_0 @ X44))),
% 0.33/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.33/0.53  thf('9', plain,
% 0.33/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.33/0.53        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.33/0.53  thf(fc1_subset_1, axiom,
% 0.33/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.33/0.53  thf('10', plain, (![X48 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 0.33/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.33/0.53  thf('11', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.33/0.53      inference('clc', [status(thm)], ['9', '10'])).
% 0.33/0.53  thf(d3_tarski, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.33/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.33/0.53  thf('12', plain,
% 0.33/0.53      (![X1 : $i, X3 : $i]:
% 0.33/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.33/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.33/0.53  thf(d4_tarski, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.33/0.53       ( ![C:$i]:
% 0.33/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.33/0.53           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.33/0.53  thf('13', plain,
% 0.33/0.53      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.33/0.53         (~ (r2_hidden @ X33 @ X34)
% 0.33/0.53          | ~ (r2_hidden @ X35 @ X33)
% 0.33/0.53          | (r2_hidden @ X35 @ X36)
% 0.33/0.53          | ((X36) != (k3_tarski @ X34)))),
% 0.33/0.53      inference('cnf', [status(esa)], [d4_tarski])).
% 0.33/0.53  thf('14', plain,
% 0.33/0.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.33/0.53         ((r2_hidden @ X35 @ (k3_tarski @ X34))
% 0.33/0.53          | ~ (r2_hidden @ X35 @ X33)
% 0.33/0.53          | ~ (r2_hidden @ X33 @ X34))),
% 0.33/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.33/0.53  thf('15', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.53         ((r1_tarski @ X0 @ X1)
% 0.33/0.53          | ~ (r2_hidden @ X0 @ X2)
% 0.33/0.53          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['12', '14'])).
% 0.33/0.53  thf('16', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))
% 0.33/0.53          | (r1_tarski @ sk_B @ X0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['11', '15'])).
% 0.33/0.53  thf(t99_zfmisc_1, axiom,
% 0.33/0.53    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.33/0.53  thf('17', plain, (![X42 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X42)) = (X42))),
% 0.33/0.53      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.33/0.53  thf('18', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A) | (r1_tarski @ sk_B @ X0))),
% 0.33/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.33/0.53  thf('19', plain,
% 0.33/0.53      (![X1 : $i, X3 : $i]:
% 0.33/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.33/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.33/0.53  thf('20', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.33/0.53  thf('21', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.33/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.33/0.53  thf(t12_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.33/0.53  thf('22', plain,
% 0.33/0.53      (![X4 : $i, X5 : $i]:
% 0.33/0.53         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.33/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.33/0.53  thf('23', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.33/0.53  thf('24', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (sk_A))),
% 0.33/0.53      inference('demod', [status(thm)], ['6', '23'])).
% 0.33/0.53  thf('25', plain,
% 0.33/0.53      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.33/0.53         != (k2_subset_1 @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('26', plain, (![X46 : $i]: ((k2_subset_1 @ X46) = (X46))),
% 0.33/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.33/0.53  thf('27', plain, (![X46 : $i]: ((k2_subset_1 @ X46) = (X46))),
% 0.33/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.33/0.53  thf('28', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.33/0.53      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.33/0.53  thf('29', plain, ($false),
% 0.33/0.53      inference('simplify_reflect-', [status(thm)], ['24', '28'])).
% 0.33/0.53  
% 0.33/0.53  % SZS output end Refutation
% 0.33/0.53  
% 0.39/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
