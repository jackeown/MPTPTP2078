%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BvZJMOyNSq

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  40 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  137 ( 234 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t218_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ C @ A ) )
         => ( v5_relat_1 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v5_relat_1 @ C @ A ) )
           => ( v5_relat_1 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t218_relat_1])).

thf('0',plain,(
    ~ ( v5_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('8',plain,
    ( sk_A
    = ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( v5_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BvZJMOyNSq
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:14:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 27 iterations in 0.008s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.44  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.44  thf(t218_relat_1, conjecture,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.44       ( ![C:$i]:
% 0.19/0.44         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) ) =>
% 0.19/0.44           ( v5_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (~( ![A:$i,B:$i]:
% 0.19/0.44        ( ( r1_tarski @ A @ B ) =>
% 0.19/0.44          ( ![C:$i]:
% 0.19/0.44            ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) ) =>
% 0.19/0.44              ( v5_relat_1 @ C @ B ) ) ) ) )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t218_relat_1])).
% 0.19/0.44  thf('0', plain, (~ (v5_relat_1 @ sk_C @ sk_B)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(d19_relat_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( v1_relat_1 @ B ) =>
% 0.19/0.44       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.44  thf('3', plain,
% 0.19/0.44      (![X20 : $i, X21 : $i]:
% 0.19/0.44         (~ (v5_relat_1 @ X20 @ X21)
% 0.19/0.44          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.19/0.44          | ~ (v1_relat_1 @ X20))),
% 0.19/0.44      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.44  thf('4', plain,
% 0.19/0.44      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.44  thf('5', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('6', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.19/0.44      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.44  thf(t45_xboole_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.44       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.19/0.44  thf('7', plain,
% 0.19/0.44      (![X10 : $i, X11 : $i]:
% 0.19/0.44         (((X11) = (k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))
% 0.19/0.44          | ~ (r1_tarski @ X10 @ X11))),
% 0.19/0.44      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.19/0.44  thf('8', plain,
% 0.19/0.44      (((sk_A)
% 0.19/0.44         = (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 0.19/0.44            (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 0.19/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.44  thf(t11_xboole_1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i]:
% 0.19/0.44     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.19/0.44  thf('9', plain,
% 0.19/0.44      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.44         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.19/0.44      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.19/0.44  thf('10', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.44  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.19/0.44      inference('sup-', [status(thm)], ['1', '10'])).
% 0.19/0.44  thf('12', plain,
% 0.19/0.44      (![X20 : $i, X21 : $i]:
% 0.19/0.44         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.19/0.44          | (v5_relat_1 @ X20 @ X21)
% 0.19/0.44          | ~ (v1_relat_1 @ X20))),
% 0.19/0.44      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.44  thf('13', plain, ((~ (v1_relat_1 @ sk_C) | (v5_relat_1 @ sk_C @ sk_B))),
% 0.19/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.44  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('15', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.19/0.44      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.44  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
