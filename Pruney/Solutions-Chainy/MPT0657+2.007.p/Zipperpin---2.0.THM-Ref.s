%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X9Vk0vqT88

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:41 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 133 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  459 (1932 expanded)
%              Number of equality atoms :   47 ( 212 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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

thf('0',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ X2 )
        = ( k4_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('7',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

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

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X6 )
       != X5 )
      | ( ( k5_relat_1 @ X6 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k5_relat_1 @ X4 @ X7 )
       != ( k6_relat_1 @ X5 ) )
      | ( X7 = X6 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('14',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7 = X6 )
      | ( ( k5_relat_1 @ X4 @ X7 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ( ( k5_relat_1 @ X6 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
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
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('24',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('29',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('30',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k4_relat_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17','20','21','27','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k4_relat_1 @ sk_A )
      = sk_B )
    | ( ( k5_relat_1 @ sk_B @ sk_A )
     != ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k4_relat_1 @ sk_A )
      = sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k4_relat_1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('42',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X9Vk0vqT88
% 0.16/0.38  % Computer   : n024.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 16:36:21 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.56  % Solved by: fo/fo7.sh
% 0.24/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.56  % done 61 iterations in 0.070s
% 0.24/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.56  % SZS output start Refutation
% 0.24/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.24/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.24/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.24/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.56  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.24/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.24/0.56  thf(t64_funct_1, conjecture,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.56           ( ( ( v2_funct_1 @ A ) & 
% 0.24/0.56               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.24/0.56               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.24/0.56             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.24/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.56    (~( ![A:$i]:
% 0.24/0.56        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.56          ( ![B:$i]:
% 0.24/0.56            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.56              ( ( ( v2_funct_1 @ A ) & 
% 0.24/0.56                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.24/0.56                  ( ( k5_relat_1 @ B @ A ) =
% 0.24/0.56                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.24/0.56                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.24/0.56    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.24/0.56  thf('0', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(d9_funct_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.56       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.24/0.56  thf('1', plain,
% 0.24/0.56      (![X2 : $i]:
% 0.24/0.56         (~ (v2_funct_1 @ X2)
% 0.24/0.56          | ((k2_funct_1 @ X2) = (k4_relat_1 @ X2))
% 0.24/0.56          | ~ (v1_funct_1 @ X2)
% 0.24/0.56          | ~ (v1_relat_1 @ X2))),
% 0.24/0.56      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.24/0.56  thf('2', plain,
% 0.24/0.56      ((~ (v1_funct_1 @ sk_A)
% 0.24/0.56        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.24/0.56        | ~ (v2_funct_1 @ sk_A))),
% 0.24/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.56  thf('3', plain, ((v1_funct_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('4', plain, ((v2_funct_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('5', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.24/0.56  thf(t61_funct_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.56       ( ( v2_funct_1 @ A ) =>
% 0.24/0.56         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.24/0.56             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.24/0.56           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.24/0.56             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.24/0.56  thf('6', plain,
% 0.24/0.56      (![X8 : $i]:
% 0.24/0.56         (~ (v2_funct_1 @ X8)
% 0.24/0.56          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.24/0.56              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.24/0.56          | ~ (v1_funct_1 @ X8)
% 0.24/0.56          | ~ (v1_relat_1 @ X8))),
% 0.24/0.56      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.24/0.56  thf('7', plain,
% 0.24/0.56      ((((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.24/0.56          = (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.24/0.56        | ~ (v1_relat_1 @ sk_A)
% 0.24/0.56        | ~ (v1_funct_1 @ sk_A)
% 0.24/0.56        | ~ (v2_funct_1 @ sk_A))),
% 0.24/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.24/0.56  thf('8', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('10', plain, ((v1_funct_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('11', plain, ((v2_funct_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('12', plain,
% 0.24/0.56      (((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.24/0.56         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 0.24/0.56      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.24/0.56  thf(l72_funct_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.56       ( ![C:$i]:
% 0.24/0.56         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.56           ( ![D:$i]:
% 0.24/0.56             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.24/0.56               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 0.24/0.56                   ( ( k5_relat_1 @ B @ C ) =
% 0.24/0.56                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.24/0.56                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.24/0.56                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 0.24/0.56  thf('13', plain,
% 0.24/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X4)
% 0.24/0.56          | ~ (v1_funct_1 @ X4)
% 0.24/0.56          | ((k2_relat_1 @ X6) != (X5))
% 0.24/0.56          | ((k5_relat_1 @ X6 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.24/0.56          | ((k5_relat_1 @ X4 @ X7) != (k6_relat_1 @ X5))
% 0.24/0.56          | ((X7) = (X6))
% 0.24/0.56          | ~ (v1_funct_1 @ X7)
% 0.24/0.56          | ~ (v1_relat_1 @ X7)
% 0.24/0.56          | ~ (v1_funct_1 @ X6)
% 0.24/0.56          | ~ (v1_relat_1 @ X6))),
% 0.24/0.56      inference('cnf', [status(esa)], [l72_funct_1])).
% 0.24/0.56  thf('14', plain,
% 0.24/0.56      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X6)
% 0.24/0.56          | ~ (v1_funct_1 @ X6)
% 0.24/0.56          | ~ (v1_relat_1 @ X7)
% 0.24/0.56          | ~ (v1_funct_1 @ X7)
% 0.24/0.56          | ((X7) = (X6))
% 0.24/0.56          | ((k5_relat_1 @ X4 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.24/0.56          | ((k5_relat_1 @ X6 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.24/0.56          | ~ (v1_funct_1 @ X4)
% 0.24/0.56          | ~ (v1_relat_1 @ X4))),
% 0.24/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.24/0.56  thf('15', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.24/0.56            != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.24/0.56          | ~ (v1_relat_1 @ sk_A)
% 0.24/0.56          | ~ (v1_funct_1 @ sk_A)
% 0.24/0.56          | ((k5_relat_1 @ X0 @ sk_A)
% 0.24/0.56              != (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.24/0.56          | ((k4_relat_1 @ sk_A) = (X0))
% 0.24/0.56          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.24/0.56          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.24/0.56          | ~ (v1_funct_1 @ X0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['12', '14'])).
% 0.24/0.56  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('17', plain, ((v1_funct_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(t37_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.24/0.56         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.24/0.56  thf('19', plain,
% 0.24/0.56      (![X1 : $i]:
% 0.24/0.56         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 0.24/0.56          | ~ (v1_relat_1 @ X1))),
% 0.24/0.56      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.24/0.56  thf('20', plain,
% 0.24/0.56      (((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.24/0.56  thf('21', plain,
% 0.24/0.56      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('22', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.24/0.56  thf(dt_k2_funct_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.24/0.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.24/0.56  thf('23', plain,
% 0.24/0.56      (![X3 : $i]:
% 0.24/0.56         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.24/0.56          | ~ (v1_funct_1 @ X3)
% 0.24/0.56          | ~ (v1_relat_1 @ X3))),
% 0.24/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.24/0.56  thf('24', plain,
% 0.24/0.56      (((v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.24/0.56        | ~ (v1_relat_1 @ sk_A)
% 0.24/0.56        | ~ (v1_funct_1 @ sk_A))),
% 0.24/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.24/0.56  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('27', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.24/0.56  thf('28', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.24/0.56  thf('29', plain,
% 0.24/0.56      (![X3 : $i]:
% 0.24/0.56         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.24/0.56          | ~ (v1_funct_1 @ X3)
% 0.24/0.56          | ~ (v1_relat_1 @ X3))),
% 0.24/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.24/0.56  thf('30', plain,
% 0.24/0.56      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.24/0.56        | ~ (v1_relat_1 @ sk_A)
% 0.24/0.56        | ~ (v1_funct_1 @ sk_A))),
% 0.24/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.24/0.56  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('32', plain, ((v1_funct_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('33', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.24/0.56  thf('34', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.24/0.56            != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.24/0.56          | ((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.24/0.56          | ((k4_relat_1 @ sk_A) = (X0))
% 0.24/0.56          | ~ (v1_funct_1 @ X0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0))),
% 0.24/0.56      inference('demod', [status(thm)],
% 0.24/0.56                ['15', '16', '17', '20', '21', '27', '33'])).
% 0.24/0.56  thf('35', plain,
% 0.24/0.56      ((~ (v1_relat_1 @ sk_B)
% 0.24/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.24/0.56        | ((k4_relat_1 @ sk_A) = (sk_B))
% 0.24/0.56        | ((k5_relat_1 @ sk_B @ sk_A) != (k5_relat_1 @ sk_B @ sk_A)))),
% 0.24/0.56      inference('eq_res', [status(thm)], ['34'])).
% 0.24/0.56  thf('36', plain,
% 0.24/0.56      ((((k4_relat_1 @ sk_A) = (sk_B))
% 0.24/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.24/0.56        | ~ (v1_relat_1 @ sk_B))),
% 0.24/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.24/0.56  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('39', plain, (((k4_relat_1 @ sk_A) = (sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.24/0.56  thf('40', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('41', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.24/0.56  thf('42', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.24/0.56  thf('43', plain, ($false),
% 0.24/0.56      inference('simplify_reflect-', [status(thm)], ['39', '42'])).
% 0.24/0.56  
% 0.24/0.56  % SZS output end Refutation
% 0.24/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
