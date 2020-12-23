%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sIgDshyjJq

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:26 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  263 ( 318 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( X7
       != ( k1_wellord2 @ X6 ) )
      | ( ( k3_relat_1 @ X7 )
        = X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X6: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X6 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X6 ) )
        = X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_B @ X4 ) @ ( k3_relat_1 @ X4 ) )
      | ( v1_relat_2 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7
       != ( k1_wellord2 @ X6 ) )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X9 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X7 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('14',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X6 ) )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k1_wellord2 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ X6 )
      | ~ ( r2_hidden @ X8 @ X6 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('16',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k1_wellord2 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ X6 )
      | ~ ( r2_hidden @ X8 @ X6 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ X4 ) @ ( sk_B @ X4 ) ) @ X4 )
      | ( v1_relat_2 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sIgDshyjJq
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:15:21 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 25 iterations in 0.029s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.51  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.23/0.51  thf(t2_wellord2, conjecture, (![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t2_wellord2])).
% 0.23/0.51  thf('0', plain, (~ (v1_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(d1_wellord2, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.23/0.51         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.23/0.51           ( ![C:$i,D:$i]:
% 0.23/0.51             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.23/0.51               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.23/0.51                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i]:
% 0.23/0.51         (((X7) != (k1_wellord2 @ X6))
% 0.23/0.51          | ((k3_relat_1 @ X7) = (X6))
% 0.23/0.51          | ~ (v1_relat_1 @ X7))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X6 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ (k1_wellord2 @ X6))
% 0.23/0.51          | ((k3_relat_1 @ (k1_wellord2 @ X6)) = (X6)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.23/0.51  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.23/0.51  thf('3', plain, (![X10 : $i]: (v1_relat_1 @ (k1_wellord2 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.23/0.51  thf('4', plain, (![X6 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X6)) = (X6))),
% 0.23/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.51  thf(l1_wellord1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) =>
% 0.23/0.51       ( ( v1_relat_2 @ A ) <=>
% 0.23/0.51         ( ![B:$i]:
% 0.23/0.51           ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) =>
% 0.23/0.51             ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) ))).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X4 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_B @ X4) @ (k3_relat_1 @ X4))
% 0.23/0.51          | (v1_relat_2 @ X4)
% 0.23/0.51          | ~ (v1_relat_1 @ X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.23/0.51          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.51  thf('7', plain, (![X10 : $i]: (v1_relat_1 @ (k1_wellord2 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.23/0.51          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.23/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf(d3_tarski, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X1 : $i, X3 : $i]:
% 0.23/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.23/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X1 : $i, X3 : $i]:
% 0.23/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.23/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.51  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.23/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.51         (((X7) != (k1_wellord2 @ X6))
% 0.23/0.51          | ~ (r2_hidden @ X8 @ X6)
% 0.23/0.51          | ~ (r2_hidden @ X9 @ X6)
% 0.23/0.51          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ X7)
% 0.23/0.51          | ~ (r1_tarski @ X8 @ X9)
% 0.23/0.51          | ~ (v1_relat_1 @ X7))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ (k1_wellord2 @ X6))
% 0.23/0.51          | ~ (r1_tarski @ X8 @ X9)
% 0.23/0.51          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ (k1_wellord2 @ X6))
% 0.23/0.51          | ~ (r2_hidden @ X9 @ X6)
% 0.23/0.51          | ~ (r2_hidden @ X8 @ X6))),
% 0.23/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.51  thf('15', plain, (![X10 : $i]: (v1_relat_1 @ (k1_wellord2 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.23/0.51         (~ (r1_tarski @ X8 @ X9)
% 0.23/0.51          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ (k1_wellord2 @ X6))
% 0.23/0.51          | ~ (r2_hidden @ X9 @ X6)
% 0.23/0.51          | ~ (r2_hidden @ X8 @ X6))),
% 0.23/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.51          | ~ (r2_hidden @ X0 @ X1)
% 0.23/0.51          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['12', '16'])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.23/0.51          | ~ (r2_hidden @ X0 @ X1))),
% 0.23/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v1_relat_2 @ (k1_wellord2 @ X0))
% 0.23/0.51          | (r2_hidden @ 
% 0.23/0.51             (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.23/0.51              (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.23/0.51             (k1_wellord2 @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['8', '18'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X4 : $i]:
% 0.23/0.51         (~ (r2_hidden @ (k4_tarski @ (sk_B @ X4) @ (sk_B @ X4)) @ X4)
% 0.23/0.51          | (v1_relat_2 @ X4)
% 0.23/0.51          | ~ (v1_relat_1 @ X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v1_relat_2 @ (k1_wellord2 @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.23/0.51          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.51  thf('22', plain, (![X10 : $i]: (v1_relat_1 @ (k1_wellord2 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v1_relat_2 @ (k1_wellord2 @ X0)) | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.23/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.23/0.51  thf('24', plain, (![X0 : $i]: (v1_relat_2 @ (k1_wellord2 @ X0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.51  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
