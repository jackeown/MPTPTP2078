%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L5y3qzSTNf

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  209 ( 231 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t29_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_relat_2 @ ( k1_wellord2 @ A ) @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_relat_2 @ ( k1_wellord2 @ A ) @ A ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord2])).

thf('0',plain,(
    ~ ( r1_relat_2 @ ( k1_wellord2 @ sk_A ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_relat_2 @ A @ B )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
             => ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r1_relat_2 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7
       != ( k1_wellord2 @ X6 ) )
      | ( ( k3_relat_1 @ X7 )
        = X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('3',plain,(
    ! [X6: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X6 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X6 ) )
        = X6 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_2 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k3_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(t2_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_wellord2])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_relat_2 @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_C @ X0 @ X1 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_C @ X0 @ X1 ) ) @ X1 )
      | ( r1_relat_2 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('15',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L5y3qzSTNf
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 15 iterations in 0.017s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.21/0.47  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(t29_wellord2, conjecture,
% 0.21/0.47    (![A:$i]: ( r1_relat_2 @ ( k1_wellord2 @ A ) @ A ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]: ( r1_relat_2 @ ( k1_wellord2 @ A ) @ A ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t29_wellord2])).
% 0.21/0.47  thf('0', plain, (~ (r1_relat_2 @ (k1_wellord2 @ sk_A) @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d1_relat_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( r1_relat_2 @ A @ B ) <=>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( r2_hidden @ C @ B ) =>
% 0.21/0.47               ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.21/0.47          | (r1_relat_2 @ X1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.21/0.47  thf(d1_wellord2, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.47         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.47           ( ![C:$i,D:$i]:
% 0.21/0.47             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.47               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.47                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (((X7) != (k1_wellord2 @ X6))
% 0.21/0.47          | ((k3_relat_1 @ X7) = (X6))
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X6 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (k1_wellord2 @ X6))
% 0.21/0.47          | ((k3_relat_1 @ (k1_wellord2 @ X6)) = (X6)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.47  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.47  thf('4', plain, (![X10 : $i]: (v1_relat_1 @ (k1_wellord2 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.47  thf('5', plain, (![X6 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X6)) = (X6))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(l1_wellord1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( v1_relat_2 @ A ) <=>
% 0.21/0.47         ( ![B:$i]:
% 0.21/0.47           ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) =>
% 0.21/0.47             ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (~ (v1_relat_2 @ X4)
% 0.21/0.47          | (r2_hidden @ (k4_tarski @ X5 @ X5) @ X4)
% 0.21/0.47          | ~ (r2_hidden @ X5 @ (k3_relat_1 @ X4))
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.47          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (k1_wellord2 @ X0))
% 0.21/0.47          | ~ (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, (![X10 : $i]: (v1_relat_1 @ (k1_wellord2 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.47  thf(t2_wellord2, axiom, (![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.47  thf('9', plain, (![X11 : $i]: (v1_relat_2 @ (k1_wellord2 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_wellord2])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.47          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (k1_wellord2 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X1)
% 0.21/0.47          | (r1_relat_2 @ X1 @ X0)
% 0.21/0.47          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_C @ X0 @ X1)) @ 
% 0.21/0.47             (k1_wellord2 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_C @ X0 @ X1)) @ X1)
% 0.21/0.47          | (r1_relat_2 @ X1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.47          | (r1_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, (![X10 : $i]: (v1_relat_1 @ (k1_wellord2 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.47  thf('15', plain, (![X10 : $i]: (v1_relat_1 @ (k1_wellord2 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.47          | (r1_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.47  thf('17', plain, (![X0 : $i]: (r1_relat_2 @ (k1_wellord2 @ X0) @ X0)),
% 0.21/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.47  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
