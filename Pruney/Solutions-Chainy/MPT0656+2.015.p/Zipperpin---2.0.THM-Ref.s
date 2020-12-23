%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pDIn9NKsI7

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:38 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 135 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  499 (1937 expanded)
%              Number of equality atoms :   43 ( 205 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t63_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ( ( k5_relat_1 @ A @ B )
                  = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_funct_1])).

thf('1',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X8 ) @ X8 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('10',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('27',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('35',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','40','41'])).

thf('43',plain,
    ( ( sk_B
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( sk_B
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('48',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pDIn9NKsI7
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 48 iterations in 0.044s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.35/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.35/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.54  thf(t78_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ A ) =>
% 0.35/0.54       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (![X3 : $i]:
% 0.35/0.54         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 0.35/0.55          | ~ (v1_relat_1 @ X3))),
% 0.35/0.55      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.35/0.55  thf(t63_funct_1, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.55           ( ( ( v2_funct_1 @ A ) & 
% 0.35/0.55               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.35/0.55               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.35/0.55             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.55              ( ( ( v2_funct_1 @ A ) & 
% 0.35/0.55                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.35/0.55                  ( ( k5_relat_1 @ A @ B ) =
% 0.35/0.55                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.35/0.55                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(fc5_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.35/0.55       ( ( v1_relat_1 @ ( k4_relat_1 @ A ) ) & 
% 0.35/0.55         ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (![X6 : $i]:
% 0.35/0.55         ((v1_relat_1 @ (k4_relat_1 @ X6))
% 0.35/0.55          | ~ (v2_funct_1 @ X6)
% 0.35/0.55          | ~ (v1_funct_1 @ X6)
% 0.35/0.55          | ~ (v1_relat_1 @ X6))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.35/0.55  thf('3', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(d9_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (![X5 : $i]:
% 0.35/0.55         (~ (v2_funct_1 @ X5)
% 0.35/0.55          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.35/0.55          | ~ (v1_funct_1 @ X5)
% 0.35/0.55          | ~ (v1_relat_1 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      ((~ (v1_funct_1 @ sk_A)
% 0.35/0.55        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.35/0.55        | ~ (v2_funct_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.55  thf('6', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('7', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('8', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.35/0.55  thf(t61_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ( v2_funct_1 @ A ) =>
% 0.35/0.55         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.35/0.55             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.35/0.55           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.35/0.55             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (![X8 : $i]:
% 0.35/0.55         (~ (v2_funct_1 @ X8)
% 0.35/0.55          | ((k5_relat_1 @ (k2_funct_1 @ X8) @ X8)
% 0.35/0.55              = (k6_relat_1 @ (k2_relat_1 @ X8)))
% 0.35/0.55          | ~ (v1_funct_1 @ X8)
% 0.35/0.55          | ~ (v1_relat_1 @ X8))),
% 0.35/0.55      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.35/0.55          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_A)
% 0.35/0.55        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.55        | ~ (v2_funct_1 @ sk_A))),
% 0.35/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.35/0.55  thf('11', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('13', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('14', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.35/0.55         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.35/0.55  thf(t55_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( v1_relat_1 @ B ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( v1_relat_1 @ C ) =>
% 0.35/0.55               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.35/0.55                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X0)
% 0.35/0.55          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.35/0.55              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 0.35/0.55          | ~ (v1_relat_1 @ X2)
% 0.35/0.55          | ~ (v1_relat_1 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.35/0.55            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.35/0.55          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.35/0.55          | ~ (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ sk_A))),
% 0.35/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.35/0.55  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.35/0.55            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.35/0.55          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.35/0.55          | ~ (v1_relat_1 @ X0))),
% 0.35/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ sk_A)
% 0.35/0.55          | ~ (v1_funct_1 @ sk_A)
% 0.35/0.55          | ~ (v2_funct_1 @ sk_A)
% 0.35/0.55          | ~ (v1_relat_1 @ X0)
% 0.35/0.55          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.35/0.55              = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['2', '19'])).
% 0.35/0.55  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('22', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('23', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X0)
% 0.35/0.55          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.35/0.55              = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 0.35/0.55      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.35/0.55          = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ 
% 0.35/0.55             (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.55      inference('sup+', [status(thm)], ['1', '24'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (![X6 : $i]:
% 0.35/0.55         ((v1_relat_1 @ (k4_relat_1 @ X6))
% 0.35/0.55          | ~ (v2_funct_1 @ X6)
% 0.35/0.55          | ~ (v1_funct_1 @ X6)
% 0.35/0.55          | ~ (v1_relat_1 @ X6))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.35/0.55  thf('27', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.35/0.55  thf(t55_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ( v2_funct_1 @ A ) =>
% 0.35/0.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.35/0.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (![X7 : $i]:
% 0.35/0.55         (~ (v2_funct_1 @ X7)
% 0.35/0.55          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 0.35/0.55          | ~ (v1_funct_1 @ X7)
% 0.35/0.55          | ~ (v1_relat_1 @ X7))),
% 0.35/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      ((((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_A)
% 0.35/0.55        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.55        | ~ (v2_funct_1 @ sk_A))),
% 0.35/0.55      inference('sup+', [status(thm)], ['27', '28'])).
% 0.35/0.55  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('31', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('32', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.35/0.55  thf(t80_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) =>
% 0.35/0.55       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      (![X4 : $i]:
% 0.35/0.55         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 0.35/0.55          | ~ (v1_relat_1 @ X4))),
% 0.35/0.55      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.35/0.55          = (k4_relat_1 @ sk_A))
% 0.35/0.55        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.35/0.55  thf('36', plain,
% 0.35/0.55      ((~ (v1_relat_1 @ sk_A)
% 0.35/0.55        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.55        | ~ (v2_funct_1 @ sk_A)
% 0.35/0.55        | ((k5_relat_1 @ (k4_relat_1 @ sk_A) @ 
% 0.35/0.55            (k6_relat_1 @ (k1_relat_1 @ sk_A))) = (k4_relat_1 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['26', '35'])).
% 0.35/0.55  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('38', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('39', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.35/0.55         = (k4_relat_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.35/0.55  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.35/0.55         = (k4_relat_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['25', '40', '41'])).
% 0.35/0.55  thf('43', plain, ((((sk_B) = (k4_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.55      inference('sup+', [status(thm)], ['0', '42'])).
% 0.35/0.55  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('45', plain, (((sk_B) = (k4_relat_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['43', '44'])).
% 0.35/0.55  thf('46', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('47', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.35/0.55  thf('48', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.55  thf('49', plain, ($false),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['45', '48'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
