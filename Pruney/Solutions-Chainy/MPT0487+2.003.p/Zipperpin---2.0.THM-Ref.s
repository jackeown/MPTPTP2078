%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jY2iFIBhCE

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 105 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  449 (1416 expanded)
%              Number of equality atoms :   36 ( 148 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t82_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ! [D: $i] :
              ( ( v1_relat_1 @ D )
             => ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ! [D: $i] :
                ( ( v1_relat_1 @ D )
               => ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
                    & ( ( k5_relat_1 @ B @ C )
                      = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                    & ( ( k5_relat_1 @ C @ D )
                      = ( k6_relat_1 @ A ) ) )
                 => ( D = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_relat_1])).

thf('0',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('4',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C ) )
      = ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','19'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_D )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['0','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_D = sk_B ),
    inference(demod,[status(thm)],['26','37','42','43'])).

thf('45',plain,(
    sk_D != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jY2iFIBhCE
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:37:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 46 iterations in 0.034s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.49  thf(t82_relat_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ C ) =>
% 0.21/0.49           ( ![D:$i]:
% 0.21/0.49             ( ( v1_relat_1 @ D ) =>
% 0.21/0.49               ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) & 
% 0.21/0.49                   ( ( k5_relat_1 @ B @ C ) =
% 0.21/0.49                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.21/0.49                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.21/0.49                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( v1_relat_1 @ B ) =>
% 0.21/0.49          ( ![C:$i]:
% 0.21/0.49            ( ( v1_relat_1 @ C ) =>
% 0.21/0.49              ( ![D:$i]:
% 0.21/0.49                ( ( v1_relat_1 @ D ) =>
% 0.21/0.49                  ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) & 
% 0.21/0.49                      ( ( k5_relat_1 @ B @ C ) =
% 0.21/0.49                        ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.21/0.49                      ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.21/0.49                    ( ( D ) = ( B ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t82_relat_1])).
% 0.21/0.49  thf('0', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ (k1_relat_1 @ sk_D)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t44_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ B ) =>
% 0.21/0.49           ( r1_tarski @
% 0.21/0.49             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X3)
% 0.21/0.49          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X4 @ X3)) @ 
% 0.21/0.49             (k1_relat_1 @ X4))
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ (k1_relat_1 @ sk_C))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(t71_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.49  thf('5', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.49  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.21/0.49  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t1_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.49       ( r1_tarski @ A @ C ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.49          | (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.49  thf(t46_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ B ) =>
% 0.21/0.49           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.49             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X5)
% 0.21/0.49          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) = (k1_relat_1 @ X6))
% 0.21/0.49          | ~ (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X5))
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | ((k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_C)) = (k1_relat_1 @ sk_B))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ (k1_relat_1 @ sk_D)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.49  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain, (((k1_relat_1 @ sk_D) = (k1_relat_1 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '19'])).
% 0.21/0.49  thf(t55_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ B ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( v1_relat_1 @ C ) =>
% 0.21/0.49               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.21/0.49                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.21/0.49              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.21/0.49          | ~ (v1_relat_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.21/0.49            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_C @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.21/0.49            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_C @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_D)
% 0.21/0.49          = (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ (k1_relat_1 @ sk_D)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X3)
% 0.21/0.49          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X4 @ X3)) @ 
% 0.21/0.49             (k1_relat_1 @ X4))
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D))) @ 
% 0.21/0.49         (k1_relat_1 @ sk_B))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.49  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.21/0.49  thf(t77_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.49         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.21/0.49          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 0.21/0.49          | ~ (v1_relat_1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.49        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_D) = (sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_D) = (sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t79_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.49         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.21/0.49          | ((k5_relat_1 @ X14 @ (k6_relat_1 @ X15)) = (X14))
% 0.21/0.49          | ~ (v1_relat_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, (((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, (((sk_D) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '37', '42', '43'])).
% 0.21/0.49  thf('45', plain, (((sk_D) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('46', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
