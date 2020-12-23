%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0im3a4xrRJ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  247 ( 293 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t2_wellord2,conjecture,(
    ! [A: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( v1_relat_2 @ ( k1_wellord2 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t2_wellord2])).

thf('0',plain,(
    ~ ( v1_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
       != ( k1_wellord2 @ X5 ) )
      | ( ( k3_relat_1 @ X6 )
        = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X5: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X5 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X5 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( r2_hidden @ ( sk_B @ X3 ) @ ( k3_relat_1 @ X3 ) )
      | ( v1_relat_2 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
       != ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X6 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('12',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X5 ) )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('14',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ X3 ) @ ( sk_B @ X3 ) ) @ X3 )
      | ( v1_relat_2 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0im3a4xrRJ
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 25 iterations in 0.043s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(t2_wellord2, conjecture, (![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t2_wellord2])).
% 0.20/0.50  thf('0', plain, (~ (v1_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d1_wellord2, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.20/0.50         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.50           ( ![C:$i,D:$i]:
% 0.20/0.50             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.50               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.50                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         (((X6) != (k1_wellord2 @ X5))
% 0.20/0.50          | ((k3_relat_1 @ X6) = (X5))
% 0.20/0.50          | ~ (v1_relat_1 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X5 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (k1_wellord2 @ X5))
% 0.20/0.50          | ((k3_relat_1 @ (k1_wellord2 @ X5)) = (X5)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.50  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.50  thf('3', plain, (![X9 : $i]: (v1_relat_1 @ (k1_wellord2 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.50  thf('4', plain, (![X5 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X5)) = (X5))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf(l1_wellord1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( v1_relat_2 @ A ) <=>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) =>
% 0.20/0.50             ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X3 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_B @ X3) @ (k3_relat_1 @ X3))
% 0.20/0.50          | (v1_relat_2 @ X3)
% 0.20/0.50          | ~ (v1_relat_1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.50          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, (![X9 : $i]: (v1_relat_1 @ (k1_wellord2 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.50          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (((X6) != (k1_wellord2 @ X5))
% 0.20/0.50          | ~ (r2_hidden @ X7 @ X5)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ X5)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ X6)
% 0.20/0.50          | ~ (r1_tarski @ X7 @ X8)
% 0.20/0.50          | ~ (v1_relat_1 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (k1_wellord2 @ X5))
% 0.20/0.50          | ~ (r1_tarski @ X7 @ X8)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k1_wellord2 @ X5))
% 0.20/0.50          | ~ (r2_hidden @ X8 @ X5)
% 0.20/0.50          | ~ (r2_hidden @ X7 @ X5))),
% 0.20/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.50  thf('13', plain, (![X9 : $i]: (v1_relat_1 @ (k1_wellord2 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X7 @ X8)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k1_wellord2 @ X5))
% 0.20/0.50          | ~ (r2_hidden @ X8 @ X5)
% 0.20/0.50          | ~ (r2_hidden @ X7 @ X5))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v1_relat_2 @ (k1_wellord2 @ X0))
% 0.20/0.50          | (r2_hidden @ 
% 0.20/0.50             (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.20/0.50              (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.20/0.50             (k1_wellord2 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X3 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (k4_tarski @ (sk_B @ X3) @ (sk_B @ X3)) @ X3)
% 0.20/0.50          | (v1_relat_2 @ X3)
% 0.20/0.50          | ~ (v1_relat_1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v1_relat_2 @ (k1_wellord2 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.50          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain, (![X9 : $i]: (v1_relat_1 @ (k1_wellord2 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v1_relat_2 @ (k1_wellord2 @ X0)) | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, (![X0 : $i]: (v1_relat_2 @ (k1_wellord2 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.50  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
