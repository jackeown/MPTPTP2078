%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hhgu1GW2tf

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:35 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   58 (  66 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  530 ( 608 expanded)
%              Number of equality atoms :   32 (  38 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t160_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t160_relat_1])).

thf('31',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
     != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hhgu1GW2tf
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.75/1.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.75/1.92  % Solved by: fo/fo7.sh
% 1.75/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.92  % done 1900 iterations in 1.477s
% 1.75/1.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.75/1.92  % SZS output start Refutation
% 1.75/1.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.75/1.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.75/1.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.75/1.92  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.75/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.75/1.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.75/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.75/1.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.75/1.92  thf(t148_relat_1, axiom,
% 1.75/1.92    (![A:$i,B:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ B ) =>
% 1.75/1.92       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.75/1.92  thf('0', plain,
% 1.75/1.92      (![X3 : $i, X4 : $i]:
% 1.75/1.92         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 1.75/1.92          | ~ (v1_relat_1 @ X3))),
% 1.75/1.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.75/1.92  thf(t94_relat_1, axiom,
% 1.75/1.92    (![A:$i,B:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ B ) =>
% 1.75/1.92       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.75/1.92  thf('1', plain,
% 1.75/1.92      (![X15 : $i, X16 : $i]:
% 1.75/1.92         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 1.75/1.92          | ~ (v1_relat_1 @ X16))),
% 1.75/1.92      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.75/1.92  thf(t80_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ A ) =>
% 1.75/1.92       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.75/1.92  thf('2', plain,
% 1.75/1.92      (![X14 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 1.75/1.92          | ~ (v1_relat_1 @ X14))),
% 1.75/1.92      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.75/1.92  thf(t55_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ A ) =>
% 1.75/1.92       ( ![B:$i]:
% 1.75/1.92         ( ( v1_relat_1 @ B ) =>
% 1.75/1.92           ( ![C:$i]:
% 1.75/1.92             ( ( v1_relat_1 @ C ) =>
% 1.75/1.92               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.75/1.92                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.75/1.92  thf('3', plain,
% 1.75/1.92      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X9)
% 1.75/1.92          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 1.75/1.92              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 1.75/1.92          | ~ (v1_relat_1 @ X11)
% 1.75/1.92          | ~ (v1_relat_1 @ X10))),
% 1.75/1.92      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.75/1.92  thf('4', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X0 @ X1)
% 1.75/1.92            = (k5_relat_1 @ X0 @ 
% 1.75/1.92               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 1.75/1.92      inference('sup+', [status(thm)], ['2', '3'])).
% 1.75/1.92  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.75/1.92  thf('5', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.75/1.92  thf('6', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X0 @ X1)
% 1.75/1.92            = (k5_relat_1 @ X0 @ 
% 1.75/1.92               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('demod', [status(thm)], ['4', '5'])).
% 1.75/1.92  thf('7', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k5_relat_1 @ X0 @ X1)
% 1.75/1.92              = (k5_relat_1 @ X0 @ 
% 1.75/1.92                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 1.75/1.92      inference('simplify', [status(thm)], ['6'])).
% 1.75/1.92  thf('8', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X0 @ X1)
% 1.75/1.92            = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('sup+', [status(thm)], ['1', '7'])).
% 1.75/1.92  thf('9', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ((k5_relat_1 @ X0 @ X1)
% 1.75/1.92              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 1.75/1.92      inference('simplify', [status(thm)], ['8'])).
% 1.75/1.92  thf('10', plain,
% 1.75/1.92      (![X15 : $i, X16 : $i]:
% 1.75/1.92         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 1.75/1.92          | ~ (v1_relat_1 @ X16))),
% 1.75/1.92      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.75/1.92  thf(dt_k5_relat_1, axiom,
% 1.75/1.92    (![A:$i,B:$i]:
% 1.75/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.75/1.92       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.75/1.92  thf('11', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.75/1.92  thf('12', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.75/1.92      inference('sup+', [status(thm)], ['10', '11'])).
% 1.75/1.92  thf('13', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.75/1.92  thf('14', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('demod', [status(thm)], ['12', '13'])).
% 1.75/1.92  thf('15', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.75/1.92      inference('simplify', [status(thm)], ['14'])).
% 1.75/1.92  thf('16', plain,
% 1.75/1.92      (![X15 : $i, X16 : $i]:
% 1.75/1.92         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 1.75/1.92          | ~ (v1_relat_1 @ X16))),
% 1.75/1.92      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.75/1.92  thf(t44_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ A ) =>
% 1.75/1.92       ( ![B:$i]:
% 1.75/1.92         ( ( v1_relat_1 @ B ) =>
% 1.75/1.92           ( r1_tarski @
% 1.75/1.92             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.75/1.92  thf('17', plain,
% 1.75/1.92      (![X5 : $i, X6 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X5)
% 1.75/1.92          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 1.75/1.92             (k1_relat_1 @ X6))
% 1.75/1.92          | ~ (v1_relat_1 @ X6))),
% 1.75/1.92      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.75/1.92  thf('18', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.75/1.92           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('sup+', [status(thm)], ['16', '17'])).
% 1.75/1.92  thf(t71_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.75/1.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.75/1.92  thf('19', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 1.75/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.75/1.92  thf('20', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.75/1.92  thf('21', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.75/1.92  thf('22', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X1)
% 1.75/1.92          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 1.75/1.92      inference('simplify', [status(thm)], ['21'])).
% 1.75/1.92  thf(t47_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ A ) =>
% 1.75/1.92       ( ![B:$i]:
% 1.75/1.92         ( ( v1_relat_1 @ B ) =>
% 1.75/1.92           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.75/1.92             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.75/1.92  thf('23', plain,
% 1.75/1.92      (![X7 : $i, X8 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X7)
% 1.75/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X8)) = (k2_relat_1 @ X8))
% 1.75/1.92          | ~ (r1_tarski @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X7))
% 1.75/1.92          | ~ (v1_relat_1 @ X8))),
% 1.75/1.92      inference('cnf', [status(esa)], [t47_relat_1])).
% 1.75/1.92  thf('24', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 1.75/1.92          | ((k2_relat_1 @ 
% 1.75/1.92              (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 1.75/1.92              = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('sup-', [status(thm)], ['22', '23'])).
% 1.75/1.92  thf('25', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k2_relat_1 @ 
% 1.75/1.92              (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 1.75/1.92              = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('sup-', [status(thm)], ['15', '24'])).
% 1.75/1.92  thf('26', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (((k2_relat_1 @ 
% 1.75/1.92            (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 1.75/1.92            = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('simplify', [status(thm)], ['25'])).
% 1.75/1.92  thf('27', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.75/1.92            = (k2_relat_1 @ (k7_relat_1 @ X0 @ (k2_relat_1 @ X1))))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('sup+', [status(thm)], ['9', '26'])).
% 1.75/1.92  thf('28', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.75/1.92              = (k2_relat_1 @ (k7_relat_1 @ X0 @ (k2_relat_1 @ X1)))))),
% 1.75/1.92      inference('simplify', [status(thm)], ['27'])).
% 1.75/1.92  thf('29', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 1.75/1.92            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('sup+', [status(thm)], ['0', '28'])).
% 1.75/1.92  thf('30', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 1.75/1.92              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 1.75/1.92      inference('simplify', [status(thm)], ['29'])).
% 1.75/1.92  thf(t160_relat_1, conjecture,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ A ) =>
% 1.75/1.92       ( ![B:$i]:
% 1.75/1.92         ( ( v1_relat_1 @ B ) =>
% 1.75/1.92           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.75/1.92             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.75/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.92    (~( ![A:$i]:
% 1.75/1.92        ( ( v1_relat_1 @ A ) =>
% 1.75/1.92          ( ![B:$i]:
% 1.75/1.92            ( ( v1_relat_1 @ B ) =>
% 1.75/1.92              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.75/1.92                ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 1.75/1.92    inference('cnf.neg', [status(esa)], [t160_relat_1])).
% 1.75/1.92  thf('31', plain,
% 1.75/1.92      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.75/1.92         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('32', plain,
% 1.75/1.92      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 1.75/1.92          != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 1.75/1.92        | ~ (v1_relat_1 @ sk_B)
% 1.75/1.92        | ~ (v1_relat_1 @ sk_A))),
% 1.75/1.92      inference('sup-', [status(thm)], ['30', '31'])).
% 1.75/1.92  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('35', plain,
% 1.75/1.92      (((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 1.75/1.92         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 1.75/1.92      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.75/1.92  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 1.75/1.92  
% 1.75/1.92  % SZS output end Refutation
% 1.75/1.92  
% 1.75/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
