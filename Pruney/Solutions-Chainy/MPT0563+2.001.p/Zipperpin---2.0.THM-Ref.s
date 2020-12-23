%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h8r4pZVnmW

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  304 ( 329 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X15 @ X13 @ X14 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X4
       != ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t167_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t167_relat_1])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h8r4pZVnmW
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 33 iterations in 0.050s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(d3_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf(t166_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ C ) =>
% 0.19/0.50       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.19/0.50         ( ?[D:$i]:
% 0.19/0.50           ( ( r2_hidden @ D @ B ) & 
% 0.19/0.50             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.19/0.50             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X15 @ X13 @ X14)) @ X15)
% 0.19/0.50          | ~ (v1_relat_1 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (k4_tarski @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.19/0.50              (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.19/0.50             X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf(dt_k7_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.50  thf(t98_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X16 : $i]:
% 0.19/0.50         (((k7_relat_1 @ X16 @ (k1_relat_1 @ X16)) = (X16))
% 0.19/0.50          | ~ (v1_relat_1 @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.19/0.50  thf(d11_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i,C:$i]:
% 0.19/0.50         ( ( v1_relat_1 @ C ) =>
% 0.19/0.50           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.19/0.50             ( ![D:$i,E:$i]:
% 0.19/0.50               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.19/0.50                 ( ( r2_hidden @ D @ B ) & 
% 0.19/0.50                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X4)
% 0.19/0.50          | ((X4) != (k7_relat_1 @ X5 @ X6))
% 0.19/0.50          | (r2_hidden @ X7 @ X6)
% 0.19/0.50          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ X4)
% 0.19/0.50          | ~ (v1_relat_1 @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X5)
% 0.19/0.50          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k7_relat_1 @ X5 @ X6))
% 0.19/0.50          | (r2_hidden @ X7 @ X6)
% 0.19/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ X0)
% 0.19/0.50          | ~ (v1_relat_1 @ X0)
% 0.19/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.19/0.50          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.19/0.50          | ~ (v1_relat_1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '6'])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.19/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.19/0.50          | ~ (v1_relat_1 @ X0)
% 0.19/0.50          | ~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X0)
% 0.19/0.50          | ~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ X0)
% 0.19/0.50          | ~ (v1_relat_1 @ X0)
% 0.19/0.50          | (r2_hidden @ X2 @ (k1_relat_1 @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.19/0.50          | ~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ X0)
% 0.19/0.50          | ~ (v1_relat_1 @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X0)
% 0.19/0.50          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.19/0.50          | ~ (v1_relat_1 @ X0)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 0.19/0.50             (k1_relat_1 @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 0.19/0.50           (k1_relat_1 @ X0))
% 0.19/0.50          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.19/0.50          | ~ (v1_relat_1 @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X0)
% 0.19/0.50          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.19/0.50          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.19/0.50          | ~ (v1_relat_1 @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.50  thf(t167_relat_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( v1_relat_1 @ B ) =>
% 0.19/0.50          ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t167_relat_1])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('17', plain, (~ (v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('19', plain, ($false), inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
