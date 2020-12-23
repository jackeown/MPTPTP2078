%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y2be3G2WFx

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 133 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  580 (2070 expanded)
%              Number of equality atoms :   59 ( 227 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('1',plain,(
    ! [X1: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf(t64_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
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
                & ( ( k2_relat_1 @ B )
                  = ( k1_relat_1 @ A ) )
                & ( ( k5_relat_1 @ B @ A )
                  = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_1])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('9',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf(l72_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( ( k2_relat_1 @ B )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X4 )
       != X3 )
      | ( ( k5_relat_1 @ X4 @ X2 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ( ( k5_relat_1 @ X2 @ X5 )
       != ( k6_relat_1 @ X3 ) )
      | ( X5 = X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('16',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5 = X4 )
      | ( ( k5_relat_1 @ X2 @ X5 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ( ( k5_relat_1 @ X4 @ X2 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
      | ( ( k4_relat_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k4_relat_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ( ( k4_relat_1 @ sk_A )
        = X0 )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ( ( k4_relat_1 @ sk_A )
        = X0 )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k4_relat_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k4_relat_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k4_relat_1 @ sk_A )
      = sk_B )
    | ( ( k5_relat_1 @ sk_B @ sk_A )
     != ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k4_relat_1 @ sk_A )
      = sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k4_relat_1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('46',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y2be3G2WFx
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 64 iterations in 0.056s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.50  thf(fc5_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.21/0.50       ( ( v1_relat_1 @ ( k4_relat_1 @ A ) ) & 
% 0.21/0.50         ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X1 : $i]:
% 0.21/0.50         ((v1_relat_1 @ (k4_relat_1 @ X1))
% 0.21/0.50          | ~ (v2_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X1 : $i]:
% 0.21/0.50         ((v1_funct_1 @ (k4_relat_1 @ X1))
% 0.21/0.50          | ~ (v2_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.21/0.50  thf(t64_funct_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50           ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.50               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.21/0.50               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.21/0.50             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50              ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.50                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.21/0.50                  ( ( k5_relat_1 @ B @ A ) =
% 0.21/0.50                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.21/0.50                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.21/0.50  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d9_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v2_funct_1 @ X0)
% 0.21/0.50          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.50        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.21/0.50        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.50  thf(t61_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ( v2_funct_1 @ A ) =>
% 0.21/0.50         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.21/0.50             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.50           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.21/0.50             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         (~ (v2_funct_1 @ X7)
% 0.21/0.50          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 0.21/0.50              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.21/0.50          | ~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.21/0.50          = (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.50        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.21/0.50         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.21/0.50  thf(l72_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50           ( ![D:$i]:
% 0.21/0.50             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.50               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.50                   ( ( k5_relat_1 @ B @ C ) =
% 0.21/0.50                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.21/0.50                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.21/0.50                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X2)
% 0.21/0.50          | ~ (v1_funct_1 @ X2)
% 0.21/0.50          | ((k2_relat_1 @ X4) != (X3))
% 0.21/0.50          | ((k5_relat_1 @ X4 @ X2) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.21/0.50          | ((k5_relat_1 @ X2 @ X5) != (k6_relat_1 @ X3))
% 0.21/0.50          | ((X5) = (X4))
% 0.21/0.50          | ~ (v1_funct_1 @ X5)
% 0.21/0.50          | ~ (v1_relat_1 @ X5)
% 0.21/0.50          | ~ (v1_funct_1 @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [l72_funct_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X5)
% 0.21/0.50          | ~ (v1_funct_1 @ X5)
% 0.21/0.50          | ((X5) = (X4))
% 0.21/0.50          | ((k5_relat_1 @ X2 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.21/0.50          | ((k5_relat_1 @ X4 @ X2) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.21/0.50          | ~ (v1_funct_1 @ X2)
% 0.21/0.50          | ~ (v1_relat_1 @ X2))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.21/0.50            != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_A)
% 0.21/0.50          | ((k5_relat_1 @ X0 @ sk_A)
% 0.21/0.50              != (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.21/0.50          | ((k4_relat_1 @ sk_A) = (X0))
% 0.21/0.50          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.50          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.50  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.50  thf(t55_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ( v2_funct_1 @ A ) =>
% 0.21/0.50         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.50           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X6 : $i]:
% 0.21/0.50         (~ (v2_funct_1 @ X6)
% 0.21/0.50          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 0.21/0.50          | ~ (v1_funct_1 @ X6)
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.50        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.21/0.51            != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.21/0.51          | ((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.21/0.51          | ((k4_relat_1 @ sk_A) = (X0))
% 0.21/0.51          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.51          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18', '19', '26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_A)
% 0.21/0.51          | ~ (v2_funct_1 @ sk_A)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.51          | ((k4_relat_1 @ sk_A) = (X0))
% 0.21/0.51          | ((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.21/0.51          | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.21/0.51              != (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '28'])).
% 0.21/0.51  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.51          | ((k4_relat_1 @ sk_A) = (X0))
% 0.21/0.51          | ((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.21/0.51          | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.21/0.51              != (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_A)
% 0.21/0.51          | ~ (v2_funct_1 @ sk_A)
% 0.21/0.51          | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.21/0.51              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.21/0.51          | ((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.21/0.51          | ((k4_relat_1 @ sk_A) = (X0))
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '33'])).
% 0.21/0.51  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.21/0.51            != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.21/0.51          | ((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.21/0.51          | ((k4_relat_1 @ sk_A) = (X0))
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.51        | ((k4_relat_1 @ sk_A) = (sk_B))
% 0.21/0.51        | ((k5_relat_1 @ sk_B @ sk_A) != (k5_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('eq_res', [status(thm)], ['38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((((k4_relat_1 @ sk_A) = (sk_B))
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.51  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('43', plain, (((k4_relat_1 @ sk_A) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.51  thf('44', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.51  thf('46', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
