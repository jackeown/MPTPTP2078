%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3B49JKTbCE

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 (  71 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  396 ( 564 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ X11 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,
    ( ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ X11 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k10_relat_1 @ X6 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k10_relat_1 @ X3 @ ( k10_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('26',plain,
    ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C )
      = ( k10_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k10_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3B49JKTbCE
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:59:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 28 iterations in 0.019s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(t94_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i]:
% 0.19/0.46         (((k7_relat_1 @ X12 @ X11) = (k5_relat_1 @ (k6_relat_1 @ X11) @ X12))
% 0.19/0.46          | ~ (v1_relat_1 @ X12))),
% 0.19/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.46  thf(t175_funct_2, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.46       ( ![B:$i,C:$i]:
% 0.19/0.46         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.19/0.46           ( ( k10_relat_1 @ A @ C ) =
% 0.19/0.46             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.46          ( ![B:$i,C:$i]:
% 0.19/0.46            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.19/0.46              ( ( k10_relat_1 @ A @ C ) =
% 0.19/0.46                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.19/0.46  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t71_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.46  thf('2', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.46  thf(d18_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.19/0.46          | (v4_relat_1 @ X0 @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.46          | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf(fc3_funct_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.46  thf('5', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.19/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      ((v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '6'])).
% 0.19/0.46  thf(t209_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.46       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.19/0.46          | ~ (v4_relat_1 @ X7 @ X8)
% 0.19/0.46          | ~ (v1_relat_1 @ X7))),
% 0.19/0.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.46        | ((k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.19/0.46            = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (((k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.19/0.46         = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i]:
% 0.19/0.46         (((k7_relat_1 @ X12 @ X11) = (k5_relat_1 @ (k6_relat_1 @ X11) @ X12))
% 0.19/0.46          | ~ (v1_relat_1 @ X12))),
% 0.19/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.46  thf('13', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.46  thf(t182_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( v1_relat_1 @ B ) =>
% 0.19/0.46           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.46             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X5 : $i, X6 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X5)
% 0.19/0.46          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.19/0.46              = (k10_relat_1 @ X6 @ (k1_relat_1 @ X5)))
% 0.19/0.46          | ~ (v1_relat_1 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.46            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.46          | ~ (v1_relat_1 @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf('16', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.46            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.46          | ~ (v1_relat_1 @ X1))),
% 0.19/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.46            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.19/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.19/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['12', '17'])).
% 0.19/0.46  thf('19', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('20', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.46           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.19/0.46      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (((k1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.46         = (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['11', '21'])).
% 0.19/0.46  thf('23', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.46         = (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.46      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.46  thf(t181_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ![C:$i]:
% 0.19/0.46         ( ( v1_relat_1 @ C ) =>
% 0.19/0.46           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.19/0.46             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X2)
% 0.19/0.46          | ((k10_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.19/0.46              = (k10_relat_1 @ X3 @ (k10_relat_1 @ X2 @ X4)))
% 0.19/0.46          | ~ (v1_relat_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      ((((k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C)
% 0.19/0.46          = (k10_relat_1 @ sk_A @ sk_C))
% 0.19/0.46        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.19/0.46        | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.46      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.46  thf('27', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('29', plain,
% 0.19/0.46      (((k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C)
% 0.19/0.46         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.46  thf('30', plain,
% 0.19/0.46      ((((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.19/0.46          = (k10_relat_1 @ sk_A @ sk_C))
% 0.19/0.46        | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.46      inference('sup+', [status(thm)], ['0', '29'])).
% 0.19/0.46  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('32', plain,
% 0.19/0.46      (((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.19/0.46         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.46  thf('33', plain,
% 0.19/0.46      (((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.46         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('34', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
