%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YLKrlDxK0p

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  179 ( 204 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X14 @ X12 @ X13 ) @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k2_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k2_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t144_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_relat_1])).

thf('9',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YLKrlDxK0p
% 0.13/0.36  % Computer   : n011.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:48:27 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 26 iterations in 0.037s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.51  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.51  thf(d3_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i]:
% 0.22/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf(t143_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ C ) =>
% 0.22/0.51       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.22/0.51         ( ?[D:$i]:
% 0.22/0.51           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.51             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.22/0.51             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X14 @ X12 @ X13) @ X13) @ X14)
% 0.22/0.51          | ~ (v1_relat_1 @ X14))),
% 0.22/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X1)
% 0.22/0.51          | (r2_hidden @ 
% 0.22/0.51             (k4_tarski @ 
% 0.22/0.51              (sk_D_2 @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.22/0.51              (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.22/0.51             X1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf(d5_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]:
% 0.22/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.22/0.51          | (r2_hidden @ X5 @ X7)
% 0.22/0.51          | ((X7) != (k2_relat_1 @ X6)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((r2_hidden @ X5 @ (k2_relat_1 @ X6))
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.22/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.22/0.51             (k2_relat_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i]:
% 0.22/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.51  thf(t144_relat_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i]:
% 0.22/0.51        ( ( v1_relat_1 @ B ) =>
% 0.22/0.51          ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t144_relat_1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('10', plain, (~ (v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('12', plain, ($false), inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
