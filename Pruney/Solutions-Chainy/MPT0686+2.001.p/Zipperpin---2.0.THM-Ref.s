%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jiTNeaHlBs

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  268 ( 368 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t141_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_xboole_0 @ B @ C )
         => ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_xboole_0 @ B @ C )
           => ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t141_funct_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X10 @ X11 ) @ ( k10_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X8 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X8 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ X2 @ ( sk_C @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ X1 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X2 @ ( sk_C @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ X1 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    ~ ( r1_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['12','13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jiTNeaHlBs
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 48 iterations in 0.060s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(t141_funct_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ![B:$i,C:$i]:
% 0.20/0.51         ( ( r1_xboole_0 @ B @ C ) =>
% 0.20/0.51           ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51          ( ![B:$i,C:$i]:
% 0.20/0.51            ( ( r1_xboole_0 @ B @ C ) =>
% 0.20/0.51              ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t141_funct_1])).
% 0.20/0.51  thf('0', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t137_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.20/0.51         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (((k10_relat_1 @ X10 @ (k3_xboole_0 @ X11 @ X12))
% 0.20/0.51            = (k3_xboole_0 @ (k10_relat_1 @ X10 @ X11) @ 
% 0.20/0.51               (k10_relat_1 @ X10 @ X12)))
% 0.20/0.51          | ~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.20/0.51  thf(t4_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ 
% 0.20/0.51           (sk_C @ (k10_relat_1 @ X2 @ X0) @ (k10_relat_1 @ X2 @ X1)) @ 
% 0.20/0.51           (k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.51          | ~ (v1_relat_1 @ X2)
% 0.20/0.51          | ~ (v1_funct_1 @ X2)
% 0.20/0.51          | (r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(d13_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ![B:$i,C:$i]:
% 0.20/0.51         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.20/0.51           ( ![D:$i]:
% 0.20/0.51             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.51                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         (((X7) != (k10_relat_1 @ X6 @ X5))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ X6 @ X8) @ X5)
% 0.20/0.51          | ~ (r2_hidden @ X8 @ X7)
% 0.20/0.51          | ~ (v1_funct_1 @ X6)
% 0.20/0.51          | ~ (v1_relat_1 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X6)
% 0.20/0.51          | ~ (v1_funct_1 @ X6)
% 0.20/0.51          | ~ (r2_hidden @ X8 @ (k10_relat_1 @ X6 @ X5))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ X6 @ X8) @ X5))),
% 0.20/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X2)
% 0.20/0.51          | ~ (v1_relat_1 @ X2)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k1_funct_1 @ X2 @ 
% 0.20/0.51              (sk_C @ (k10_relat_1 @ X2 @ X0) @ (k10_relat_1 @ X2 @ X1))) @ 
% 0.20/0.51             (k3_xboole_0 @ X1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X2)
% 0.20/0.51          | ~ (v1_relat_1 @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ 
% 0.20/0.51           (k1_funct_1 @ X2 @ 
% 0.20/0.51            (sk_C @ (k10_relat_1 @ X2 @ X0) @ (k10_relat_1 @ X2 @ X1))) @ 
% 0.20/0.51           (k3_xboole_0 @ X1 @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X2)
% 0.20/0.51          | ~ (v1_funct_1 @ X2)
% 0.20/0.51          | (r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X2)
% 0.20/0.51          | ~ (v1_relat_1 @ X2)
% 0.20/0.51          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.20/0.51             (k10_relat_1 @ X0 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (~ (r1_xboole_0 @ (k10_relat_1 @ sk_A @ sk_B) @ 
% 0.20/0.51          (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain, ((~ (v1_funct_1 @ sk_A) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('15', plain, ($false),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
