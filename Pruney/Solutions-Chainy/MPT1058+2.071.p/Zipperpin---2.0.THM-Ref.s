%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wru0Nf5WLy

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 (  87 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  436 ( 693 expanded)
%              Number of equality atoms :   33 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k10_relat_1 @ X4 @ ( k10_relat_1 @ X3 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

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

thf('2',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,
    ( ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k10_relat_1 @ X4 @ ( k10_relat_1 @ X3 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('30',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','30'])).

thf('32',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wru0Nf5WLy
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:08:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 21 iterations in 0.017s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(t94_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (((k7_relat_1 @ X11 @ X10) = (k5_relat_1 @ (k6_relat_1 @ X10) @ X11))
% 0.22/0.49          | ~ (v1_relat_1 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.49  thf(t181_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( v1_relat_1 @ C ) =>
% 0.22/0.49           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.22/0.49             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X3)
% 0.22/0.49          | ((k10_relat_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 0.22/0.49              = (k10_relat_1 @ X4 @ (k10_relat_1 @ X3 @ X5)))
% 0.22/0.49          | ~ (v1_relat_1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.22/0.49  thf(t175_funct_2, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.49       ( ![B:$i,C:$i]:
% 0.22/0.49         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.22/0.49           ( ( k10_relat_1 @ A @ C ) =
% 0.22/0.49             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.49          ( ![B:$i,C:$i]:
% 0.22/0.49            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.22/0.49              ( ( k10_relat_1 @ A @ C ) =
% 0.22/0.49                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.22/0.49  thf('2', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t71_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.49  thf('3', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.49  thf(d18_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.22/0.49          | (v4_relat_1 @ X0 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.49          | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf(fc3_funct_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.49  thf('6', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      ((v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '7'])).
% 0.22/0.49  thf(t209_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.22/0.49          | ~ (v4_relat_1 @ X6 @ X7)
% 0.22/0.49          | ~ (v1_relat_1 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.22/0.49        | ((k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.22/0.49            = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (((k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.22/0.49         = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (((k7_relat_1 @ X11 @ X10) = (k5_relat_1 @ (k6_relat_1 @ X10) @ X11))
% 0.22/0.49          | ~ (v1_relat_1 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.49  thf('14', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.49  thf(t169_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X2 : $i]:
% 0.22/0.49         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 0.22/0.49          | ~ (v1_relat_1 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.22/0.49            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.49  thf('18', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X3)
% 0.22/0.49          | ((k10_relat_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 0.22/0.49              = (k10_relat_1 @ X4 @ (k10_relat_1 @ X3 @ X5)))
% 0.22/0.49          | ~ (v1_relat_1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 0.22/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 0.22/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X1))),
% 0.22/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 0.22/0.49            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['13', '23'])).
% 0.22/0.49  thf('25', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.49  thf('26', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 0.22/0.49           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.22/0.49      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.22/0.49         (k10_relat_1 @ sk_A @ sk_C))
% 0.22/0.49         = (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['12', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.49         = (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.49          = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C))
% 0.22/0.49        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '30'])).
% 0.22/0.49  thf('32', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.49  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.49         = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.49          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '34'])).
% 0.22/0.49  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.49         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.49         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('39', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
