%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3RPytiNxyb

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:52 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   40 (  59 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  176 ( 367 expanded)
%              Number of equality atoms :   29 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t64_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( ( k1_relat_1 @ A )
              = k1_xboole_0 )
            | ( ( k2_relat_1 @ A )
              = k1_xboole_0 ) )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_relat_1])).

thf('0',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('4',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(fc13_subset_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('11',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ( k1_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','15'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3RPytiNxyb
% 0.16/0.37  % Computer   : n007.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:06:36 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 27 iterations in 0.014s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.50  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.24/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(t64_relat_1, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ A ) =>
% 0.24/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.24/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.24/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( ( v1_relat_1 @ A ) =>
% 0.24/0.50          ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.24/0.50              ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.24/0.50            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t64_relat_1])).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      ((((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.24/0.50        | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.24/0.50         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      ((((k1_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.24/0.50         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf(fc8_relat_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.24/0.50       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X4 : $i]:
% 0.24/0.50         (~ (v1_xboole_0 @ (k1_relat_1 @ X4))
% 0.24/0.50          | ~ (v1_relat_1 @ X4)
% 0.24/0.50          | (v1_xboole_0 @ X4))),
% 0.24/0.50      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.50         | (v1_xboole_0 @ sk_A)
% 0.24/0.50         | ~ (v1_relat_1 @ sk_A))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.50  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.24/0.50  thf('5', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.24/0.50  thf(fc13_subset_1, axiom, (![A:$i]: ( v1_xboole_0 @ ( k1_subset_1 @ A ) ))).
% 0.24/0.50  thf('6', plain, (![X2 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [fc13_subset_1])).
% 0.24/0.50  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.24/0.50  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (((v1_xboole_0 @ sk_A)) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.24/0.50  thf(t6_boole, axiom,
% 0.24/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t6_boole])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      ((((sk_A) = (k1_xboole_0))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.50  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('13', plain, (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.24/0.50       (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf('15', plain, ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.24/0.50      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.24/0.50  thf('16', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.24/0.50      inference('simpl_trail', [status(thm)], ['1', '15'])).
% 0.24/0.50  thf(fc9_relat_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.24/0.50       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      (![X5 : $i]:
% 0.24/0.50         (~ (v1_xboole_0 @ (k2_relat_1 @ X5))
% 0.24/0.50          | ~ (v1_relat_1 @ X5)
% 0.24/0.50          | (v1_xboole_0 @ X5))),
% 0.24/0.50      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.50        | (v1_xboole_0 @ sk_A)
% 0.24/0.50        | ~ (v1_relat_1 @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.50  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.24/0.50  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('21', plain, ((v1_xboole_0 @ sk_A)),
% 0.24/0.50      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.24/0.50  thf('22', plain,
% 0.24/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t6_boole])).
% 0.24/0.50  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.50  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('25', plain, ($false),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
