%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ufUOZhFTYv

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 188 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  578 (2653 expanded)
%              Number of equality atoms :   53 ( 279 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

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

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('13',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('16',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('22',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('23',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('24',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','35'])).

thf('37',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('39',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('41',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('44',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( sk_B
    = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['41','46','47'])).

thf('49',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','48'])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_relat_1 @ sk_A )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['4','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k4_relat_1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('58',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ufUOZhFTYv
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 60 iterations in 0.079s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.53  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.53  thf(t37_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.21/0.53         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X1 : $i]:
% 0.21/0.53         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 0.21/0.53          | ~ (v1_relat_1 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.53  thf(t78_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X5 : $i]:
% 0.21/0.53         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 0.21/0.53          | ~ (v1_relat_1 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 0.21/0.53            = (k4_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf(dt_k4_relat_1, axiom,
% 0.21/0.53    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 0.21/0.53              = (k4_relat_1 @ X0)))),
% 0.21/0.53      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.53  thf(t63_funct_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53           ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.53               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.53               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.21/0.53             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53              ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.53                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.53                  ( ( k5_relat_1 @ A @ B ) =
% 0.21/0.53                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.21/0.53                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.21/0.53  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d9_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X6 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X6)
% 0.21/0.53          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.21/0.53          | ~ (v1_funct_1 @ X6)
% 0.21/0.53          | ~ (v1_relat_1 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      ((~ (v1_funct_1 @ sk_A)
% 0.21/0.53        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.21/0.53        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.53  thf(t61_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ A ) =>
% 0.21/0.53         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.21/0.53             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.53           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.21/0.53             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X7 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X7)
% 0.21/0.53          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 0.21/0.53              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.21/0.53          | ~ (v1_funct_1 @ X7)
% 0.21/0.53          | ~ (v1_relat_1 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.21/0.53          = (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.53        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X1 : $i]:
% 0.21/0.53         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 0.21/0.53          | ~ (v1_relat_1 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('18', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.21/0.53         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.53  thf('22', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X7 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X7)
% 0.21/0.53          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 0.21/0.53              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.21/0.53          | ~ (v1_funct_1 @ X7)
% 0.21/0.53          | ~ (v1_relat_1 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.21/0.53          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.53        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.21/0.53         = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.21/0.53  thf(t55_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v1_relat_1 @ B ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( v1_relat_1 @ C ) =>
% 0.21/0.53               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.21/0.53                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X2)
% 0.21/0.53          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.21/0.53              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.21/0.53          | ~ (v1_relat_1 @ X4)
% 0.21/0.53          | ~ (v1_relat_1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ X0)
% 0.21/0.53            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ X0)
% 0.21/0.53            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ sk_A)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ X0)
% 0.21/0.53              = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '32'])).
% 0.21/0.53  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ X0)
% 0.21/0.53              = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ (k4_relat_1 @ sk_A))
% 0.21/0.53          = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ 
% 0.21/0.53             (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))))
% 0.21/0.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['20', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((k5_relat_1 @ sk_A @ sk_B)
% 0.21/0.53         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ X0)
% 0.21/0.53              = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B)
% 0.21/0.53          = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ 
% 0.21/0.53             (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X5 : $i]:
% 0.21/0.53         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 0.21/0.53          | ~ (v1_relat_1 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B) = (sk_B))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.53  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B) = (sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (((sk_B)
% 0.21/0.53         = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ 
% 0.21/0.53            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))))),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '46', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ (k4_relat_1 @ sk_A))
% 0.21/0.53          = (sk_B))
% 0.21/0.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['36', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.53        | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ 
% 0.21/0.53            (k4_relat_1 @ sk_A)) = (sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '49'])).
% 0.21/0.53  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ (k4_relat_1 @ sk_A))
% 0.21/0.53         = (sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain, ((((k4_relat_1 @ sk_A) = (sk_B)) | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['4', '52'])).
% 0.21/0.53  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain, (((k4_relat_1 @ sk_A) = (sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.53  thf('58', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.53  thf('59', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['55', '58'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
