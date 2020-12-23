%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KuEq0e1mST

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:40 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  406 ( 561 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t8_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ D ) )
     => ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ D ) )
       => ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X34 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_D ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_D ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X34 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf(t119_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_tarski @ X28 @ X29 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X23 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r2_hidden @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ X38 @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('22',plain,(
    m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X30 @ X33 ) @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X30 @ X31 ) @ ( k4_tarski @ X30 @ X32 ) @ ( k4_tarski @ X33 @ X31 ) @ ( k4_tarski @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_enumset1 @ ( k4_tarski @ X2 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ ( k4_tarski @ X2 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KuEq0e1mST
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 143 iterations in 0.076s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.55  thf(t8_relset_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.37/0.55       ( m1_subset_1 @
% 0.37/0.55         ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.37/0.55         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.37/0.55          ( m1_subset_1 @
% 0.37/0.55            ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.37/0.55            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t8_relset_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (~ (m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C_1)) @ 
% 0.37/0.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_D)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('2', plain, ((r2_hidden @ sk_C_1 @ sk_D)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t38_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.37/0.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.37/0.55         ((r1_tarski @ (k2_tarski @ X34 @ X36) @ X37)
% 0.37/0.55          | ~ (r2_hidden @ X36 @ X37)
% 0.37/0.55          | ~ (r2_hidden @ X34 @ X37))),
% 0.37/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_D)
% 0.37/0.55          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_C_1) @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '4'])).
% 0.37/0.55  thf(t69_enumset1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.55  thf('6', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf('7', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_D)),
% 0.37/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('8', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('9', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.37/0.55         ((r1_tarski @ (k2_tarski @ X34 @ X36) @ X37)
% 0.37/0.55          | ~ (r2_hidden @ X36 @ X37)
% 0.37/0.55          | ~ (r2_hidden @ X34 @ X37))),
% 0.37/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_B)
% 0.37/0.55          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf('12', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.37/0.55  thf('13', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf('14', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.37/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf(t119_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.37/0.55       ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X26 @ X27)
% 0.37/0.55          | ~ (r1_tarski @ X28 @ X29)
% 0.37/0.55          | (r1_tarski @ (k2_zfmisc_1 @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X29)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t119_zfmisc_1])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ X1) @ 
% 0.37/0.55           (k2_zfmisc_1 @ sk_B @ X0))
% 0.37/0.55          | ~ (r1_tarski @ X1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((r1_tarski @ 
% 0.37/0.55        (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C_1)) @ 
% 0.37/0.55        (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '16'])).
% 0.37/0.55  thf(d1_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.37/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X21 @ X22)
% 0.37/0.55          | (r2_hidden @ X21 @ X23)
% 0.37/0.55          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i]:
% 0.37/0.55         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 0.37/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      ((r2_hidden @ 
% 0.37/0.55        (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C_1)) @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '19'])).
% 0.37/0.55  thf(t1_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X38 : $i, X39 : $i]:
% 0.37/0.55         ((m1_subset_1 @ X38 @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 0.37/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      ((m1_subset_1 @ 
% 0.37/0.55        (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C_1)) @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf(t70_enumset1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i]:
% 0.37/0.55         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.55  thf(t71_enumset1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.55  thf(t146_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.37/0.55       ( k2_enumset1 @
% 0.37/0.55         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 0.37/0.55         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k2_tarski @ X30 @ X33) @ (k2_tarski @ X31 @ X32))
% 0.37/0.55           = (k2_enumset1 @ (k4_tarski @ X30 @ X31) @ 
% 0.37/0.55              (k4_tarski @ X30 @ X32) @ (k4_tarski @ X33 @ X31) @ 
% 0.37/0.55              (k4_tarski @ X33 @ X32)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0))
% 0.37/0.55           = (k1_enumset1 @ (k4_tarski @ X2 @ X0) @ (k4_tarski @ X1 @ X0) @ 
% 0.37/0.55              (k4_tarski @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.55  thf('27', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.37/0.55           = (k1_enumset1 @ (k4_tarski @ X2 @ X0) @ (k4_tarski @ X1 @ X0) @ 
% 0.37/0.55              (k4_tarski @ X1 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.37/0.55           = (k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['23', '28'])).
% 0.37/0.55  thf('30', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf('31', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.37/0.55           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      ((m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C_1)) @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.37/0.55      inference('demod', [status(thm)], ['22', '32'])).
% 0.37/0.55  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
