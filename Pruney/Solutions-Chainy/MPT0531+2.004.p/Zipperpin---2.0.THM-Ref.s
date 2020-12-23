%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C9wVY5AymR

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :   13
%              Number of atoms          :  354 ( 429 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t131_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t130_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( ( k8_relat_1 @ X13 @ ( k8_relat_1 @ X14 @ X15 ) )
        = ( k8_relat_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t130_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

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

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X6 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C9wVY5AymR
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 69 iterations in 0.074s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.19/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.19/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(t131_relat_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ C ) =>
% 0.19/0.53       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53         ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.53        ( ( v1_relat_1 @ C ) =>
% 0.19/0.53          ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53            ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t131_relat_1])).
% 0.19/0.53  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t130_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ C ) =>
% 0.19/0.53       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53         ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.53         (~ (r1_tarski @ X13 @ X14)
% 0.19/0.53          | ~ (v1_relat_1 @ X15)
% 0.19/0.53          | ((k8_relat_1 @ X13 @ (k8_relat_1 @ X14 @ X15))
% 0.19/0.53              = (k8_relat_1 @ X13 @ X15)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t130_relat_1])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ X0))
% 0.19/0.53            = (k8_relat_1 @ sk_A @ X0))
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf(dt_k8_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X11 : $i, X12 : $i]:
% 0.19/0.53         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.19/0.53  thf(d3_relat_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.53           ( ![C:$i,D:$i]:
% 0.19/0.53             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.19/0.53               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]:
% 0.19/0.53         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 0.19/0.53          | (r1_tarski @ X7 @ X6)
% 0.19/0.53          | ~ (v1_relat_1 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.19/0.53  thf(d12_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ B ) =>
% 0.19/0.53       ( ![C:$i]:
% 0.19/0.53         ( ( v1_relat_1 @ C ) =>
% 0.19/0.53           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 0.19/0.53             ( ![D:$i,E:$i]:
% 0.19/0.53               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.19/0.53                 ( ( r2_hidden @ E @ A ) & 
% 0.19/0.53                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.19/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.19/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X2)
% 0.19/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.19/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.19/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.53          | (r2_hidden @ 
% 0.19/0.53             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.53              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.19/0.53             X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | (r2_hidden @ 
% 0.19/0.53             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.53              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.19/0.53             X0)
% 0.19/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.53          | (r2_hidden @ 
% 0.19/0.53             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.53              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.19/0.53             X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '8'])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((r2_hidden @ 
% 0.19/0.53           (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.53            (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.19/0.53           X0)
% 0.19/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]:
% 0.19/0.53         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ 
% 0.19/0.53             X6)
% 0.19/0.53          | (r1_tarski @ X7 @ X6)
% 0.19/0.53          | ~ (v1_relat_1 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X11 : $i, X12 : $i]:
% 0.19/0.53         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.19/0.53      inference('clc', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B @ X0))
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['2', '15'])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X11 : $i, X12 : $i]:
% 0.19/0.53         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B @ X0)))),
% 0.19/0.53      inference('clc', [status(thm)], ['16', '17'])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 0.19/0.53          (k8_relat_1 @ sk_B @ sk_C_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('20', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.19/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('22', plain, ($false), inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
