%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vM0TETUh0J

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 109 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  489 (1007 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t27_finset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( v1_finset_1 @ ( k10_relat_1 @ B @ A ) ) )
       => ( v1_finset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( v1_finset_1 @ ( k10_relat_1 @ B @ A ) ) )
         => ( v1_finset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_finset_1])).

thf('0',plain,(
    ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( ( k10_relat_1 @ X4 @ ( k2_relat_1 @ X4 ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k10_relat_1 @ X7 @ X5 ) @ ( k10_relat_1 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r1_tarski @ X12 @ ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t158_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X16 @ X14 ) @ ( k10_relat_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t158_funct_1])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf(t13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_finset_1 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( v1_finset_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('20',plain,
    ( ~ ( v1_finset_1 @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) )
        = ( k9_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('24',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
      = ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    = ( k10_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t26_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
       => ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i] :
      ( ~ ( v1_finset_1 @ ( k1_relat_1 @ X19 ) )
      | ( v1_finset_1 @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t26_finset_1])).

thf('30',plain,
    ( ~ ( v1_finset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ( v1_finset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_finset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ( v1_finset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( v1_finset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_finset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( v1_finset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_finset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( v1_finset_1 @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_finset_1 @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_finset_1 @ sk_A ),
    inference(demod,[status(thm)],['20','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vM0TETUh0J
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 31 iterations in 0.022s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.49  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.49  thf(t27_finset_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.21/0.49           ( v1_finset_1 @ ( k10_relat_1 @ B @ A ) ) ) =>
% 0.21/0.49         ( v1_finset_1 @ A ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49          ( ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.21/0.49              ( v1_finset_1 @ ( k10_relat_1 @ B @ A ) ) ) =>
% 0.21/0.49            ( v1_finset_1 @ A ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t27_finset_1])).
% 0.21/0.49  thf('0', plain, (~ (v1_finset_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t169_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (((k10_relat_1 @ X4 @ (k2_relat_1 @ X4)) = (k1_relat_1 @ X4))
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.49  thf('2', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t178_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ C ) =>
% 0.21/0.49       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.49         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X5 @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X7)
% 0.21/0.49          | (r1_tarski @ (k10_relat_1 @ X7 @ X5) @ (k10_relat_1 @ X7 @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 0.21/0.49           (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.49  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.49  thf(t146_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.49         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 0.21/0.49          | (r1_tarski @ X12 @ (k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X12)))
% 0.21/0.49          | ~ (v1_relat_1 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 0.21/0.49           (k10_relat_1 @ sk_B @ 
% 0.21/0.49            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 0.21/0.49        (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf(t158_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.21/0.49           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.21/0.49         ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.49         ((r1_tarski @ X14 @ X15)
% 0.21/0.49          | ~ (v1_relat_1 @ X16)
% 0.21/0.49          | ~ (v1_funct_1 @ X16)
% 0.21/0.49          | ~ (r1_tarski @ X14 @ (k2_relat_1 @ X16))
% 0.21/0.49          | ~ (r1_tarski @ (k10_relat_1 @ X16 @ X14) @ 
% 0.21/0.49               (k10_relat_1 @ X16 @ X15)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t158_funct_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | (r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.21/0.49  thf(t13_finset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( v1_finset_1 @ B ) ) => ( v1_finset_1 @ A ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]:
% 0.21/0.49         ((v1_finset_1 @ X17)
% 0.21/0.49          | ~ (r1_tarski @ X17 @ X18)
% 0.21/0.49          | ~ (v1_finset_1 @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((~ (v1_finset_1 @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.21/0.49        | (v1_finset_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf(t148_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (((k2_relat_1 @ (k7_relat_1 @ X2 @ X3)) = (k9_relat_1 @ X2 @ X3))
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.49  thf(fc8_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.21/0.49         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10)
% 0.21/0.49          | (v1_funct_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.21/0.49  thf(dt_k7_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.49  thf(t91_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.49         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 0.21/0.49          | ((k1_relat_1 @ (k7_relat_1 @ X9 @ X8)) = (X8))
% 0.21/0.49          | ~ (v1_relat_1 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.21/0.49            = (k10_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.21/0.49         = (k10_relat_1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf(t26_finset_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.49         ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X19 : $i]:
% 0.21/0.49         (~ (v1_finset_1 @ (k1_relat_1 @ X19))
% 0.21/0.49          | (v1_finset_1 @ (k2_relat_1 @ X19))
% 0.21/0.49          | ~ (v1_funct_1 @ X19)
% 0.21/0.49          | ~ (v1_relat_1 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t26_finset_1])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((~ (v1_finset_1 @ (k10_relat_1 @ sk_B @ sk_A))
% 0.21/0.49        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.21/0.49        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.21/0.49        | (v1_finset_1 @ 
% 0.21/0.49           (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain, ((v1_finset_1 @ (k10_relat_1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.21/0.49        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.21/0.49        | (v1_finset_1 @ 
% 0.21/0.49           (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 0.21/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | (v1_finset_1 @ 
% 0.21/0.49           (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 0.21/0.49        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '32'])).
% 0.21/0.49  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((v1_finset_1 @ 
% 0.21/0.49         (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 0.21/0.49        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49        | (v1_finset_1 @ 
% 0.21/0.49           (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '35'])).
% 0.21/0.49  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((v1_finset_1 @ 
% 0.21/0.49        (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (((v1_finset_1 @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '39'])).
% 0.21/0.49  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((v1_finset_1 @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, ((v1_finset_1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '42'])).
% 0.21/0.49  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
