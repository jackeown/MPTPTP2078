%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gzgdFJG5z7

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :  503 ( 721 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(d12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k8_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ E @ A )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ ( k8_relat_1 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( k8_relat_1 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) @ X1 )
      | ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_E @ ( k8_relat_1 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ ( k8_relat_1 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) @ X1 )
      | ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X0 @ X1 )
        = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( ( k8_relat_1 @ X0 @ X1 )
        = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( ( k8_relat_1 @ X0 @ X1 )
        = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X0 @ X1 )
        = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t128_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) )
        = ( k8_relat_1 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) )
          = ( k8_relat_1 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_relat_1])).

thf('21',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_A @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_B )
     != ( k8_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k8_relat_1 @ sk_A @ sk_B )
 != ( k8_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gzgdFJG5z7
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:27:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 16 iterations in 0.036s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.50  thf(dt_k8_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.21/0.50  thf(d12_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ C ) =>
% 0.21/0.50           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 0.21/0.50             ( ![D:$i,E:$i]:
% 0.21/0.50               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.21/0.50                 ( ( r2_hidden @ E @ A ) & 
% 0.21/0.50                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X0)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 0.21/0.50          | ~ (v1_relat_1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('eq_fact', [status(thm)], ['1'])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ 
% 0.21/0.50           (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.21/0.50          | (r2_hidden @ X5 @ X1)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X2)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.21/0.50          | (r2_hidden @ X5 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ((k8_relat_1 @ X1 @ X0)
% 0.21/0.50              = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (sk_E @ (k8_relat_1 @ X1 @ X0) @ (k8_relat_1 @ X1 @ X0) @ X2) @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (sk_E @ (k8_relat_1 @ X1 @ X0) @ (k8_relat_1 @ X1 @ X0) @ X2) @ X1)
% 0.21/0.50          | ((k8_relat_1 @ X1 @ X0)
% 0.21/0.50              = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((k8_relat_1 @ X1 @ X0)
% 0.21/0.50              = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (sk_E @ (k8_relat_1 @ X1 @ X0) @ (k8_relat_1 @ X1 @ X0) @ X2) @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r2_hidden @ 
% 0.21/0.50           (sk_E @ (k8_relat_1 @ X1 @ X0) @ (k8_relat_1 @ X1 @ X0) @ X2) @ X1)
% 0.21/0.50          | ((k8_relat_1 @ X1 @ X0)
% 0.21/0.50              = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ 
% 0.21/0.50           (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ 
% 0.21/0.50           (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ 
% 0.21/0.50               (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.21/0.50          | ~ (r2_hidden @ 
% 0.21/0.50               (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 0.21/0.50          | ~ (v1_relat_1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ 
% 0.21/0.50               (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ (sk_E @ X0 @ X0 @ X1) @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (sk_E @ X0 @ X0 @ X1) @ X1)
% 0.21/0.50          | ~ (r2_hidden @ 
% 0.21/0.50               (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ (sk_E @ X0 @ X0 @ X1) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (sk_E @ X0 @ X0 @ X1) @ X1)
% 0.21/0.50          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X1)
% 0.21/0.50          | ((k8_relat_1 @ X0 @ X1)
% 0.21/0.50              = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 0.21/0.50          | ((k8_relat_1 @ X0 @ X1)
% 0.21/0.50              = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 0.21/0.50          | ((k8_relat_1 @ X0 @ X1)
% 0.21/0.50              = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1)))
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X1)
% 0.21/0.50          | ((k8_relat_1 @ X0 @ X1)
% 0.21/0.50              = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1))))),
% 0.21/0.50      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf(t128_relat_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) ) = ( k8_relat_1 @ A @ B ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( v1_relat_1 @ B ) =>
% 0.21/0.50          ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) ) =
% 0.21/0.50            ( k8_relat_1 @ A @ B ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t128_relat_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_A @ sk_B))
% 0.21/0.50         != (k8_relat_1 @ sk_A @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((((k8_relat_1 @ sk_A @ sk_B) != (k8_relat_1 @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((k8_relat_1 @ sk_A @ sk_B) != (k8_relat_1 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
