%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.abgz1l68Af

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:18 EST 2020

% Result     : Theorem 9.94s
% Output     : Refutation 9.94s
% Verified   : 
% Statistics : Number of formulae       :   45 (  55 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  427 ( 657 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t169_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( k5_relat_1 @ ( k7_relat_1 @ A @ C ) @ ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) )
              = ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( k5_relat_1 @ ( k7_relat_1 @ A @ C ) @ ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) )
                = ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_1])).

thf('15',plain,(
    ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k7_relat_1 @ sk_B @ ( k9_relat_1 @ sk_A @ sk_C ) ) )
 != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
     != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ( ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C )
     != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C )
 != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.abgz1l68Af
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 9.94/10.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.94/10.13  % Solved by: fo/fo7.sh
% 9.94/10.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.94/10.13  % done 6118 iterations in 9.687s
% 9.94/10.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.94/10.13  % SZS output start Refutation
% 9.94/10.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.94/10.13  thf(sk_B_type, type, sk_B: $i).
% 9.94/10.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.94/10.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.94/10.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.94/10.13  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 9.94/10.13  thf(sk_C_type, type, sk_C: $i).
% 9.94/10.13  thf(sk_A_type, type, sk_A: $i).
% 9.94/10.13  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 9.94/10.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.94/10.13  thf(t112_relat_1, axiom,
% 9.94/10.13    (![A:$i,B:$i]:
% 9.94/10.13     ( ( v1_relat_1 @ B ) =>
% 9.94/10.13       ( ![C:$i]:
% 9.94/10.13         ( ( v1_relat_1 @ C ) =>
% 9.94/10.13           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 9.94/10.13             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 9.94/10.13  thf('0', plain,
% 9.94/10.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.94/10.13         (~ (v1_relat_1 @ X0)
% 9.94/10.13          | ((k7_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 9.94/10.13              = (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 9.94/10.13          | ~ (v1_relat_1 @ X1))),
% 9.94/10.13      inference('cnf', [status(esa)], [t112_relat_1])).
% 9.94/10.13  thf(fc8_funct_1, axiom,
% 9.94/10.13    (![A:$i,B:$i]:
% 9.94/10.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.94/10.13       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 9.94/10.13         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 9.94/10.13  thf('1', plain,
% 9.94/10.13      (![X13 : $i, X14 : $i]:
% 9.94/10.13         (~ (v1_funct_1 @ X13)
% 9.94/10.13          | ~ (v1_relat_1 @ X13)
% 9.94/10.13          | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 9.94/10.13      inference('cnf', [status(esa)], [fc8_funct_1])).
% 9.94/10.13  thf(t148_relat_1, axiom,
% 9.94/10.13    (![A:$i,B:$i]:
% 9.94/10.13     ( ( v1_relat_1 @ B ) =>
% 9.94/10.13       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 9.94/10.13  thf('2', plain,
% 9.94/10.13      (![X3 : $i, X4 : $i]:
% 9.94/10.13         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 9.94/10.13          | ~ (v1_relat_1 @ X3))),
% 9.94/10.13      inference('cnf', [status(esa)], [t148_relat_1])).
% 9.94/10.13  thf(t94_relat_1, axiom,
% 9.94/10.13    (![A:$i,B:$i]:
% 9.94/10.13     ( ( v1_relat_1 @ B ) =>
% 9.94/10.13       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 9.94/10.13  thf('3', plain,
% 9.94/10.13      (![X9 : $i, X10 : $i]:
% 9.94/10.13         (((k7_relat_1 @ X10 @ X9) = (k5_relat_1 @ (k6_relat_1 @ X9) @ X10))
% 9.94/10.13          | ~ (v1_relat_1 @ X10))),
% 9.94/10.13      inference('cnf', [status(esa)], [t94_relat_1])).
% 9.94/10.13  thf(t80_relat_1, axiom,
% 9.94/10.13    (![A:$i]:
% 9.94/10.13     ( ( v1_relat_1 @ A ) =>
% 9.94/10.13       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 9.94/10.13  thf('4', plain,
% 9.94/10.13      (![X8 : $i]:
% 9.94/10.13         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 9.94/10.13          | ~ (v1_relat_1 @ X8))),
% 9.94/10.13      inference('cnf', [status(esa)], [t80_relat_1])).
% 9.94/10.13  thf(t55_relat_1, axiom,
% 9.94/10.13    (![A:$i]:
% 9.94/10.13     ( ( v1_relat_1 @ A ) =>
% 9.94/10.13       ( ![B:$i]:
% 9.94/10.13         ( ( v1_relat_1 @ B ) =>
% 9.94/10.13           ( ![C:$i]:
% 9.94/10.13             ( ( v1_relat_1 @ C ) =>
% 9.94/10.13               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 9.94/10.13                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 9.94/10.13  thf('5', plain,
% 9.94/10.13      (![X5 : $i, X6 : $i, X7 : $i]:
% 9.94/10.13         (~ (v1_relat_1 @ X5)
% 9.94/10.13          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 9.94/10.13              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 9.94/10.13          | ~ (v1_relat_1 @ X7)
% 9.94/10.13          | ~ (v1_relat_1 @ X6))),
% 9.94/10.13      inference('cnf', [status(esa)], [t55_relat_1])).
% 9.94/10.13  thf('6', plain,
% 9.94/10.13      (![X0 : $i, X1 : $i]:
% 9.94/10.13         (((k5_relat_1 @ X0 @ X1)
% 9.94/10.13            = (k5_relat_1 @ X0 @ 
% 9.94/10.13               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 9.94/10.13          | ~ (v1_relat_1 @ X0)
% 9.94/10.13          | ~ (v1_relat_1 @ X0)
% 9.94/10.13          | ~ (v1_relat_1 @ X1)
% 9.94/10.13          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 9.94/10.13      inference('sup+', [status(thm)], ['4', '5'])).
% 9.94/10.13  thf(fc3_funct_1, axiom,
% 9.94/10.13    (![A:$i]:
% 9.94/10.13     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 9.94/10.13       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 9.94/10.13  thf('7', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 9.94/10.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.94/10.13  thf('8', plain,
% 9.94/10.13      (![X0 : $i, X1 : $i]:
% 9.94/10.13         (((k5_relat_1 @ X0 @ X1)
% 9.94/10.13            = (k5_relat_1 @ X0 @ 
% 9.94/10.13               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 9.94/10.13          | ~ (v1_relat_1 @ X0)
% 9.94/10.13          | ~ (v1_relat_1 @ X0)
% 9.94/10.13          | ~ (v1_relat_1 @ X1))),
% 9.94/10.13      inference('demod', [status(thm)], ['6', '7'])).
% 9.94/10.13  thf('9', plain,
% 9.94/10.13      (![X0 : $i, X1 : $i]:
% 9.94/10.13         (~ (v1_relat_1 @ X1)
% 9.94/10.13          | ~ (v1_relat_1 @ X0)
% 9.94/10.13          | ((k5_relat_1 @ X0 @ X1)
% 9.94/10.13              = (k5_relat_1 @ X0 @ 
% 9.94/10.13                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 9.94/10.13      inference('simplify', [status(thm)], ['8'])).
% 9.94/10.13  thf('10', plain,
% 9.94/10.13      (![X0 : $i, X1 : $i]:
% 9.94/10.13         (((k5_relat_1 @ X0 @ X1)
% 9.94/10.13            = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 9.94/10.13          | ~ (v1_relat_1 @ X1)
% 9.94/10.13          | ~ (v1_relat_1 @ X0)
% 9.94/10.13          | ~ (v1_relat_1 @ X1))),
% 9.94/10.13      inference('sup+', [status(thm)], ['3', '9'])).
% 9.94/10.13  thf('11', plain,
% 9.94/10.13      (![X0 : $i, X1 : $i]:
% 9.94/10.13         (~ (v1_relat_1 @ X0)
% 9.94/10.13          | ~ (v1_relat_1 @ X1)
% 9.94/10.13          | ((k5_relat_1 @ X0 @ X1)
% 9.94/10.13              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 9.94/10.13      inference('simplify', [status(thm)], ['10'])).
% 9.94/10.13  thf('12', plain,
% 9.94/10.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.94/10.13         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 9.94/10.13            = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 9.94/10.13               (k7_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 9.94/10.13          | ~ (v1_relat_1 @ X1)
% 9.94/10.13          | ~ (v1_relat_1 @ X2)
% 9.94/10.13          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 9.94/10.13      inference('sup+', [status(thm)], ['2', '11'])).
% 9.94/10.13  thf('13', plain,
% 9.94/10.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.94/10.13         (~ (v1_relat_1 @ X1)
% 9.94/10.13          | ~ (v1_funct_1 @ X1)
% 9.94/10.13          | ~ (v1_relat_1 @ X2)
% 9.94/10.13          | ~ (v1_relat_1 @ X1)
% 9.94/10.13          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 9.94/10.13              = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 9.94/10.13                 (k7_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0)))))),
% 9.94/10.13      inference('sup-', [status(thm)], ['1', '12'])).
% 9.94/10.13  thf('14', plain,
% 9.94/10.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.94/10.13         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 9.94/10.13            = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 9.94/10.13               (k7_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 9.94/10.13          | ~ (v1_relat_1 @ X2)
% 9.94/10.13          | ~ (v1_funct_1 @ X1)
% 9.94/10.13          | ~ (v1_relat_1 @ X1))),
% 9.94/10.13      inference('simplify', [status(thm)], ['13'])).
% 9.94/10.13  thf(t169_funct_1, conjecture,
% 9.94/10.13    (![A:$i]:
% 9.94/10.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.94/10.13       ( ![B:$i]:
% 9.94/10.13         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.94/10.13           ( ![C:$i]:
% 9.94/10.13             ( ( k5_relat_1 @
% 9.94/10.13                 ( k7_relat_1 @ A @ C ) @ 
% 9.94/10.13                 ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) ) =
% 9.94/10.13               ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) ) ))).
% 9.94/10.13  thf(zf_stmt_0, negated_conjecture,
% 9.94/10.13    (~( ![A:$i]:
% 9.94/10.13        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.94/10.13          ( ![B:$i]:
% 9.94/10.13            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.94/10.13              ( ![C:$i]:
% 9.94/10.13                ( ( k5_relat_1 @
% 9.94/10.13                    ( k7_relat_1 @ A @ C ) @ 
% 9.94/10.13                    ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) ) =
% 9.94/10.13                  ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) ) ) )),
% 9.94/10.13    inference('cnf.neg', [status(esa)], [t169_funct_1])).
% 9.94/10.13  thf('15', plain,
% 9.94/10.13      (((k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ 
% 9.94/10.13         (k7_relat_1 @ sk_B @ (k9_relat_1 @ sk_A @ sk_C)))
% 9.94/10.13         != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 9.94/10.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.13  thf('16', plain,
% 9.94/10.13      ((((k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 9.94/10.13          != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 9.94/10.13        | ~ (v1_relat_1 @ sk_A)
% 9.94/10.13        | ~ (v1_funct_1 @ sk_A)
% 9.94/10.13        | ~ (v1_relat_1 @ sk_B))),
% 9.94/10.13      inference('sup-', [status(thm)], ['14', '15'])).
% 9.94/10.13  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 9.94/10.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.13  thf('18', plain, ((v1_funct_1 @ sk_A)),
% 9.94/10.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.13  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 9.94/10.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.13  thf('20', plain,
% 9.94/10.13      (((k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 9.94/10.13         != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 9.94/10.13      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 9.94/10.13  thf('21', plain,
% 9.94/10.13      ((((k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C)
% 9.94/10.13          != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 9.94/10.13        | ~ (v1_relat_1 @ sk_A)
% 9.94/10.13        | ~ (v1_relat_1 @ sk_B))),
% 9.94/10.13      inference('sup-', [status(thm)], ['0', '20'])).
% 9.94/10.13  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 9.94/10.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.13  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 9.94/10.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.13  thf('24', plain,
% 9.94/10.13      (((k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C)
% 9.94/10.13         != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 9.94/10.13      inference('demod', [status(thm)], ['21', '22', '23'])).
% 9.94/10.13  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 9.94/10.13  
% 9.94/10.13  % SZS output end Refutation
% 9.94/10.13  
% 9.94/10.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
