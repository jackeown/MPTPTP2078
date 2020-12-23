%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EHENOVrud8

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  193 ( 218 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k1_wellord1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('2',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_wellord1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t13_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_wellord1])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EHENOVrud8
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 22 iterations in 0.025s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.21/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.45  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.45  thf(d3_tarski, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      (![X1 : $i, X3 : $i]:
% 0.21/0.45         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.45  thf(d1_wellord1, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( v1_relat_1 @ A ) =>
% 0.21/0.45       ( ![B:$i,C:$i]:
% 0.21/0.45         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.21/0.45           ( ![D:$i]:
% 0.21/0.45             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.45               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.45         (((X10) != (k1_wellord1 @ X9 @ X8))
% 0.21/0.45          | (r2_hidden @ (k4_tarski @ X11 @ X8) @ X9)
% 0.21/0.45          | ~ (r2_hidden @ X11 @ X10)
% 0.21/0.45          | ~ (v1_relat_1 @ X9))),
% 0.21/0.45      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ X9)
% 0.21/0.45          | ~ (r2_hidden @ X11 @ (k1_wellord1 @ X9 @ X8))
% 0.21/0.45          | (r2_hidden @ (k4_tarski @ X11 @ X8) @ X9))),
% 0.21/0.45      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 0.21/0.45          | (r2_hidden @ 
% 0.21/0.45             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 0.21/0.45          | ~ (v1_relat_1 @ X1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['0', '2'])).
% 0.21/0.45  thf(t30_relat_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( v1_relat_1 @ C ) =>
% 0.21/0.45       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.45         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.45           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.45         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.21/0.45          | (r2_hidden @ X4 @ (k3_relat_1 @ X6))
% 0.21/0.45          | ~ (v1_relat_1 @ X6))),
% 0.21/0.45      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ X0)
% 0.21/0.45          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.21/0.45          | ~ (v1_relat_1 @ X0)
% 0.21/0.45          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.21/0.45             (k3_relat_1 @ X0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         ((r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.21/0.45           (k3_relat_1 @ X0))
% 0.21/0.45          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.21/0.45          | ~ (v1_relat_1 @ X0))),
% 0.21/0.45      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X1 : $i, X3 : $i]:
% 0.21/0.45         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ X0)
% 0.21/0.45          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 0.21/0.45          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 0.21/0.45          | ~ (v1_relat_1 @ X0))),
% 0.21/0.45      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.45  thf(t13_wellord1, conjecture,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( v1_relat_1 @ B ) =>
% 0.21/0.45       ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i]:
% 0.21/0.45        ( ( v1_relat_1 @ B ) =>
% 0.21/0.45          ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t13_wellord1])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (~ (r1_tarski @ (k1_wellord1 @ sk_B @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('11', plain, (~ (v1_relat_1 @ sk_B)),
% 0.21/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.45  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('13', plain, ($false), inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
