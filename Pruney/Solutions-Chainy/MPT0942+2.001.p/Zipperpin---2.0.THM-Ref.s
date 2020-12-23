%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eJNlTk07u9

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:27 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 144 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(t4_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X4 ) )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_wellord2])).

thf(t6_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v1_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_wellord1 @ ( k1_wellord2 @ X6 ) )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_wellord2])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf(t7_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_wellord2])).

thf('3',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v4_relat_2 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v8_relat_2 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(t5_wellord2,axiom,(
    ! [A: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t5_wellord2])).

thf(t3_wellord2,axiom,(
    ! [A: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_wellord2])).

thf(t2_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_wellord2])).

thf('9',plain,
    ( ~ ( v1_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eJNlTk07u9
% 0.13/0.38  % Computer   : n010.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 11:53:15 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 13 iterations in 0.011s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.23/0.48  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.23/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.48  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.23/0.48  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.23/0.48  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.23/0.48  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.23/0.48  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.23/0.48  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.23/0.48  thf(t4_wellord2, axiom,
% 0.23/0.48    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ))).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      (![X4 : $i]: ((v6_relat_2 @ (k1_wellord2 @ X4)) | ~ (v3_ordinal1 @ X4))),
% 0.23/0.48      inference('cnf', [status(esa)], [t4_wellord2])).
% 0.23/0.48  thf(t6_wellord2, axiom,
% 0.23/0.48    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v1_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      (![X6 : $i]: ((v1_wellord1 @ (k1_wellord2 @ X6)) | ~ (v3_ordinal1 @ X6))),
% 0.23/0.48      inference('cnf', [status(esa)], [t6_wellord2])).
% 0.23/0.48  thf(d4_wellord1, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( v1_relat_1 @ A ) =>
% 0.23/0.48       ( ( v2_wellord1 @ A ) <=>
% 0.23/0.48         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.23/0.48           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (~ (v1_relat_2 @ X0)
% 0.23/0.48          | ~ (v8_relat_2 @ X0)
% 0.23/0.48          | ~ (v4_relat_2 @ X0)
% 0.23/0.48          | ~ (v6_relat_2 @ X0)
% 0.23/0.48          | ~ (v1_wellord1 @ X0)
% 0.23/0.48          | (v2_wellord1 @ X0)
% 0.23/0.48          | ~ (v1_relat_1 @ X0))),
% 0.23/0.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.23/0.48  thf(t7_wellord2, conjecture,
% 0.23/0.48    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i]:
% 0.23/0.48        ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t7_wellord2])).
% 0.23/0.48  thf('3', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_A))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('4', plain,
% 0.23/0.48      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.23/0.48        | ~ (v1_wellord1 @ (k1_wellord2 @ sk_A))
% 0.23/0.48        | ~ (v6_relat_2 @ (k1_wellord2 @ sk_A))
% 0.23/0.48        | ~ (v4_relat_2 @ (k1_wellord2 @ sk_A))
% 0.23/0.48        | ~ (v8_relat_2 @ (k1_wellord2 @ sk_A))
% 0.23/0.48        | ~ (v1_relat_2 @ (k1_wellord2 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.48  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.23/0.48  thf('5', plain, (![X1 : $i]: (v1_relat_1 @ (k1_wellord2 @ X1))),
% 0.23/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.23/0.48  thf(t5_wellord2, axiom, (![A:$i]: ( v4_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.23/0.48  thf('6', plain, (![X5 : $i]: (v4_relat_2 @ (k1_wellord2 @ X5))),
% 0.23/0.48      inference('cnf', [status(esa)], [t5_wellord2])).
% 0.23/0.48  thf(t3_wellord2, axiom, (![A:$i]: ( v8_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.23/0.48  thf('7', plain, (![X3 : $i]: (v8_relat_2 @ (k1_wellord2 @ X3))),
% 0.23/0.48      inference('cnf', [status(esa)], [t3_wellord2])).
% 0.23/0.48  thf(t2_wellord2, axiom, (![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.23/0.48  thf('8', plain, (![X2 : $i]: (v1_relat_2 @ (k1_wellord2 @ X2))),
% 0.23/0.48      inference('cnf', [status(esa)], [t2_wellord2])).
% 0.23/0.48  thf('9', plain,
% 0.23/0.48      ((~ (v1_wellord1 @ (k1_wellord2 @ sk_A))
% 0.23/0.48        | ~ (v6_relat_2 @ (k1_wellord2 @ sk_A)))),
% 0.23/0.48      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.23/0.48  thf('10', plain,
% 0.23/0.48      ((~ (v3_ordinal1 @ sk_A) | ~ (v6_relat_2 @ (k1_wellord2 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['1', '9'])).
% 0.23/0.48  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('12', plain, (~ (v6_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.23/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.23/0.48  thf('13', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.23/0.48      inference('sup-', [status(thm)], ['0', '12'])).
% 0.23/0.48  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('15', plain, ($false), inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
