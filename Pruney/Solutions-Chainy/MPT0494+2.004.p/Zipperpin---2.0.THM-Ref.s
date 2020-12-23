%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7CDJhL19Gi

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  166 ( 218 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t49_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ X4 ) @ ( k5_relat_1 @ X2 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t49_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t92_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( r1_tarski @ ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) @ ( k5_relat_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( r1_tarski @ ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) @ ( k5_relat_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t92_relat_1])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_C ) @ ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    $false ),
    inference(demod,[status(thm)],['8','9','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7CDJhL19Gi
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 7 iterations in 0.010s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(dt_k7_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.46  thf(t88_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i]:
% 0.20/0.46         ((r1_tarski @ (k7_relat_1 @ X5 @ X6) @ X5) | ~ (v1_relat_1 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.20/0.46  thf(t49_relat_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( v1_relat_1 @ B ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( v1_relat_1 @ C ) =>
% 0.20/0.46               ( ( r1_tarski @ A @ B ) =>
% 0.20/0.46                 ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X2)
% 0.20/0.46          | ~ (r1_tarski @ X3 @ X2)
% 0.20/0.46          | (r1_tarski @ (k5_relat_1 @ X3 @ X4) @ (k5_relat_1 @ X2 @ X4))
% 0.20/0.46          | ~ (v1_relat_1 @ X4)
% 0.20/0.46          | ~ (v1_relat_1 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t49_relat_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.46          | ~ (v1_relat_1 @ X2)
% 0.20/0.46          | (r1_tarski @ (k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.20/0.46             (k5_relat_1 @ X0 @ X2))
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((r1_tarski @ (k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.20/0.46           (k5_relat_1 @ X0 @ X2))
% 0.20/0.46          | ~ (v1_relat_1 @ X2)
% 0.20/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ X2)
% 0.20/0.46          | (r1_tarski @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.20/0.46             (k5_relat_1 @ X1 @ X2)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((r1_tarski @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.20/0.46           (k5_relat_1 @ X1 @ X2))
% 0.20/0.46          | ~ (v1_relat_1 @ X2)
% 0.20/0.46          | ~ (v1_relat_1 @ X1))),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf(t92_relat_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( v1_relat_1 @ C ) =>
% 0.20/0.46           ( r1_tarski @
% 0.20/0.46             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) @ 
% 0.20/0.46             ( k5_relat_1 @ B @ C ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( v1_relat_1 @ B ) =>
% 0.20/0.46          ( ![C:$i]:
% 0.20/0.46            ( ( v1_relat_1 @ C ) =>
% 0.20/0.46              ( r1_tarski @
% 0.20/0.46                ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) @ 
% 0.20/0.46                ( k5_relat_1 @ B @ C ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t92_relat_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (~ (r1_tarski @ (k5_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_C) @ 
% 0.20/0.46          (k5_relat_1 @ sk_B @ sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain, ($false),
% 0.20/0.46      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
