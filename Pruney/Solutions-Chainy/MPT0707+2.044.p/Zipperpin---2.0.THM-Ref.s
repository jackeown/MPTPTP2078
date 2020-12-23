%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t5OXef7wFk

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  75 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 ( 521 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t162_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X18: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X14: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k9_relat_1 @ X5 @ ( k9_relat_1 @ X6 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_B )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('25',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('26',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t5OXef7wFk
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 32 iterations in 0.030s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(t162_funct_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52          ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t162_funct_1])).
% 0.21/0.52  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t3_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('2', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(t71_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.52  thf('3', plain, (![X14 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf(t79_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.52         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.21/0.52          | ((k5_relat_1 @ X15 @ (k6_relat_1 @ X16)) = (X15))
% 0.21/0.52          | ~ (v1_relat_1 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.21/0.52              = (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf(fc24_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.52       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.52  thf('6', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.52          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.21/0.52              = (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.21/0.52         = (k6_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.52  thf('9', plain, (![X18 : $i]: (v4_relat_1 @ (k6_relat_1 @ X18) @ X18)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf(t209_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.21/0.52          | ~ (v4_relat_1 @ X8 @ X9)
% 0.21/0.52          | ~ (v1_relat_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf(t148_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.21/0.52          | ~ (v1_relat_1 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain, (![X14 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf('17', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.52  thf(t159_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ C ) =>
% 0.21/0.52           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.52             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X5)
% 0.21/0.52          | ((k9_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.21/0.52              = (k9_relat_1 @ X5 @ (k9_relat_1 @ X6 @ X7)))
% 0.21/0.52          | ~ (v1_relat_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.21/0.52            = (k9_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.21/0.52            = (k9_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((((k9_relat_1 @ (k6_relat_1 @ sk_B) @ sk_B)
% 0.21/0.52          = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.21/0.52        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['8', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.52  thf('25', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('26', plain, (((sk_B) = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.52  thf('27', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
