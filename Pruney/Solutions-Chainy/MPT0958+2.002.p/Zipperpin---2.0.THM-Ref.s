%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nGN533zAvi

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  236 ( 284 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d4_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r4_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) )
             => ( C = D ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X4 ) @ ( sk_C_1 @ X3 @ X4 ) ) @ X4 )
      | ( r4_relat_2 @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X4 )
      | ( r4_relat_2 @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf(l3_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) )
           => ( B = C ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( X2 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v4_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 )
      | ( r4_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_relat_2 @ X0 @ X1 )
      | ( ( sk_D @ X1 @ X0 )
        = ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v4_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( sk_C_1 @ X1 @ X0 ) )
      | ( r4_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( sk_C_1 @ X3 @ X4 )
       != ( sk_D @ X3 @ X4 ) )
      | ( r4_relat_2 @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ X1 @ X0 )
       != ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_relat_2 @ X0 @ X1 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_relat_2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( r4_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t31_wellord2,conjecture,(
    ! [A: $i] :
      ( r4_relat_2 @ ( k1_wellord2 @ A ) @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r4_relat_2 @ ( k1_wellord2 @ A ) @ A ) ),
    inference('cnf.neg',[status(esa)],[t31_wellord2])).

thf('10',plain,(
    ~ ( r4_relat_2 @ ( k1_wellord2 @ sk_A ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v4_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(t5_wellord2,axiom,(
    ! [A: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t5_wellord2])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['11','12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nGN533zAvi
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 14 iterations in 0.015s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.46  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.20/0.46  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.46  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(d4_relat_2, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( r4_relat_2 @ A @ B ) <=>
% 0.20/0.46           ( ![C:$i,D:$i]:
% 0.20/0.46             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.20/0.46                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 0.20/0.46                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) =>
% 0.20/0.46               ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         ((r2_hidden @ (k4_tarski @ (sk_D @ X3 @ X4) @ (sk_C_1 @ X3 @ X4)) @ X4)
% 0.20/0.46          | (r4_relat_2 @ X4 @ X3)
% 0.20/0.46          | ~ (v1_relat_1 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X4)
% 0.20/0.46          | (r4_relat_2 @ X4 @ X3)
% 0.20/0.46          | ~ (v1_relat_1 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.46  thf(l3_wellord1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ( v4_relat_2 @ A ) <=>
% 0.20/0.46         ( ![B:$i,C:$i]:
% 0.20/0.46           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 0.20/0.46               ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) =>
% 0.20/0.46             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v4_relat_2 @ X0)
% 0.20/0.46          | ((X2) = (X1))
% 0.20/0.46          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.20/0.46          | ~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l3_wellord1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r4_relat_2 @ X0 @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (r2_hidden @ 
% 0.20/0.46               (k4_tarski @ (sk_D @ X1 @ X0) @ (sk_C_1 @ X1 @ X0)) @ X0)
% 0.20/0.46          | ((sk_D @ X1 @ X0) = (sk_C_1 @ X1 @ X0))
% 0.20/0.46          | ~ (v4_relat_2 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v4_relat_2 @ X0)
% 0.20/0.46          | ((sk_D @ X1 @ X0) = (sk_C_1 @ X1 @ X0))
% 0.20/0.46          | ~ (r2_hidden @ 
% 0.20/0.46               (k4_tarski @ (sk_D @ X1 @ X0) @ (sk_C_1 @ X1 @ X0)) @ X0)
% 0.20/0.46          | (r4_relat_2 @ X0 @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r4_relat_2 @ X0 @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r4_relat_2 @ X0 @ X1)
% 0.20/0.46          | ((sk_D @ X1 @ X0) = (sk_C_1 @ X1 @ X0))
% 0.20/0.46          | ~ (v4_relat_2 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v4_relat_2 @ X0)
% 0.20/0.46          | ((sk_D @ X1 @ X0) = (sk_C_1 @ X1 @ X0))
% 0.20/0.46          | (r4_relat_2 @ X0 @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         (((sk_C_1 @ X3 @ X4) != (sk_D @ X3 @ X4))
% 0.20/0.46          | (r4_relat_2 @ X4 @ X3)
% 0.20/0.46          | ~ (v1_relat_1 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (((sk_C_1 @ X1 @ X0) != (sk_C_1 @ X1 @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r4_relat_2 @ X0 @ X1)
% 0.20/0.46          | ~ (v4_relat_2 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r4_relat_2 @ X0 @ X1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v4_relat_2 @ X0) | (r4_relat_2 @ X0 @ X1) | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.46  thf(t31_wellord2, conjecture,
% 0.20/0.46    (![A:$i]: ( r4_relat_2 @ ( k1_wellord2 @ A ) @ A ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]: ( r4_relat_2 @ ( k1_wellord2 @ A ) @ A ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t31_wellord2])).
% 0.20/0.46  thf('10', plain, (~ (r4_relat_2 @ (k1_wellord2 @ sk_A) @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.20/0.46        | ~ (v4_relat_2 @ (k1_wellord2 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.46  thf('12', plain, (![X8 : $i]: (v1_relat_1 @ (k1_wellord2 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.46  thf(t5_wellord2, axiom, (![A:$i]: ( v4_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.46  thf('13', plain, (![X9 : $i]: (v4_relat_2 @ (k1_wellord2 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [t5_wellord2])).
% 0.20/0.46  thf('14', plain, ($false),
% 0.20/0.46      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
