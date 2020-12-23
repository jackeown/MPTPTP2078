%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GkL399FNnS

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  91 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  353 (1273 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t48_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B )
        & ( v5_ordinal1 @ B ) )
     => ! [C: $i] :
          ( ( v3_ordinal1 @ C )
         => ( ( v1_relat_1 @ ( k7_relat_1 @ B @ C ) )
            & ( v5_relat_1 @ ( k7_relat_1 @ B @ C ) @ A )
            & ( v1_funct_1 @ ( k7_relat_1 @ B @ C ) )
            & ( v5_ordinal1 @ ( k7_relat_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v5_relat_1 @ B @ A )
          & ( v1_funct_1 @ B )
          & ( v5_ordinal1 @ B ) )
       => ! [C: $i] :
            ( ( v3_ordinal1 @ C )
           => ( ( v1_relat_1 @ ( k7_relat_1 @ B @ C ) )
              & ( v5_relat_1 @ ( k7_relat_1 @ B @ C ) @ A )
              & ( v1_funct_1 @ ( k7_relat_1 @ B @ C ) )
              & ( v5_ordinal1 @ ( k7_relat_1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_ordinal1])).

thf('0',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A )
   <= ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) )
   <= ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(fc5_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v5_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v5_relat_1 @ ( k7_relat_1 @ A @ B ) @ ( k2_relat_1 @ A ) )
        & ( v5_ordinal1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_ordinal1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ( v5_ordinal1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_ordinal1])).

thf('15',plain,
    ( ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( v3_ordinal1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v5_ordinal1 @ sk_B ) )
   <= ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,
    ( ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','13','21','22'])).

thf('24',plain,(
    ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('26',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc25_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_relat_1 @ C ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ C @ B ) )
        & ( v5_relat_1 @ ( k5_relat_1 @ C @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v5_relat_1 @ ( k5_relat_1 @ X7 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc25_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k5_relat_1 @ X0 @ sk_B ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k5_relat_1 @ X0 @ sk_B ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['24','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GkL399FNnS
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 31 iterations in 0.016s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.47  thf(t48_ordinal1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 0.21/0.47         ( v5_ordinal1 @ B ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( v3_ordinal1 @ C ) =>
% 0.21/0.47           ( ( v1_relat_1 @ ( k7_relat_1 @ B @ C ) ) & 
% 0.21/0.47             ( v5_relat_1 @ ( k7_relat_1 @ B @ C ) @ A ) & 
% 0.21/0.47             ( v1_funct_1 @ ( k7_relat_1 @ B @ C ) ) & 
% 0.21/0.47             ( v5_ordinal1 @ ( k7_relat_1 @ B @ C ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 0.21/0.47            ( v5_ordinal1 @ B ) ) =>
% 0.21/0.47          ( ![C:$i]:
% 0.21/0.47            ( ( v3_ordinal1 @ C ) =>
% 0.21/0.47              ( ( v1_relat_1 @ ( k7_relat_1 @ B @ C ) ) & 
% 0.21/0.47                ( v5_relat_1 @ ( k7_relat_1 @ B @ C ) @ A ) & 
% 0.21/0.47                ( v1_funct_1 @ ( k7_relat_1 @ B @ C ) ) & 
% 0.21/0.47                ( v5_ordinal1 @ ( k7_relat_1 @ B @ C ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t48_ordinal1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.21/0.47        | ~ (v5_relat_1 @ (k7_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.21/0.47        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.21/0.47        | ~ (v5_ordinal1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((~ (v5_relat_1 @ (k7_relat_1 @ sk_B @ sk_C) @ sk_A))
% 0.21/0.47         <= (~ ((v5_relat_1 @ (k7_relat_1 @ sk_B @ sk_C) @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(fc8_funct_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.21/0.47         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         (~ (v1_funct_1 @ X12)
% 0.21/0.47          | ~ (v1_relat_1 @ X12)
% 0.21/0.47          | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.21/0.47         <= (~ ((v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B)))
% 0.21/0.47         <= (~ ((v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain, (((v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         (~ (v1_funct_1 @ X12)
% 0.21/0.47          | ~ (v1_relat_1 @ X12)
% 0.21/0.47          | (v1_funct_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.21/0.47         <= (~ ((v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B)))
% 0.21/0.47         <= (~ ((v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain, (((v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.47  thf(fc5_ordinal1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v5_ordinal1 @ A ) & 
% 0.21/0.47         ( v3_ordinal1 @ B ) ) =>
% 0.21/0.47       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.21/0.47         ( v5_relat_1 @ ( k7_relat_1 @ A @ B ) @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.47         ( v5_ordinal1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X14 : $i, X15 : $i]:
% 0.21/0.47         (~ (v5_ordinal1 @ X14)
% 0.21/0.47          | ~ (v1_funct_1 @ X14)
% 0.21/0.47          | ~ (v1_relat_1 @ X14)
% 0.21/0.47          | ~ (v3_ordinal1 @ X15)
% 0.21/0.47          | (v5_ordinal1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc5_ordinal1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((~ (v5_ordinal1 @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.21/0.47         <= (~ ((v5_ordinal1 @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (((~ (v3_ordinal1 @ sk_C)
% 0.21/0.47         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.47         | ~ (v1_funct_1 @ sk_B)
% 0.21/0.47         | ~ (v5_ordinal1 @ sk_B)))
% 0.21/0.47         <= (~ ((v5_ordinal1 @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain, ((v3_ordinal1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain, ((v5_ordinal1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain, (((v5_ordinal1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (~ ((v5_relat_1 @ (k7_relat_1 @ sk_B @ sk_C) @ sk_A)) | 
% 0.21/0.47       ~ ((v5_ordinal1 @ (k7_relat_1 @ sk_B @ sk_C))) | 
% 0.21/0.47       ~ ((v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))) | 
% 0.21/0.47       ~ ((v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('23', plain, (~ ((v5_relat_1 @ (k7_relat_1 @ sk_B @ sk_C) @ sk_A))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['7', '13', '21', '22'])).
% 0.21/0.47  thf('24', plain, (~ (v5_relat_1 @ (k7_relat_1 @ sk_B @ sk_C) @ sk_A)),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.21/0.47  thf(t94_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k7_relat_1 @ X1 @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.47  thf('26', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(fc25_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_relat_1 @ C ) ) =>
% 0.21/0.47       ( ( v1_relat_1 @ ( k5_relat_1 @ C @ B ) ) & 
% 0.21/0.47         ( v5_relat_1 @ ( k5_relat_1 @ C @ B ) @ A ) ) ))).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (v5_relat_1 @ X5 @ X6)
% 0.21/0.47          | ~ (v1_relat_1 @ X5)
% 0.21/0.47          | ~ (v1_relat_1 @ X7)
% 0.21/0.47          | (v5_relat_1 @ (k5_relat_1 @ X7 @ X5) @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc25_relat_1])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v5_relat_1 @ (k5_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v5_relat_1 @ (k5_relat_1 @ X0 @ sk_B) @ sk_A) | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v5_relat_1 @ (k7_relat_1 @ sk_B @ X0) @ sk_A)
% 0.21/0.47          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['25', '30'])).
% 0.21/0.47  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(fc24_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.47       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('33', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_B @ X0) @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.47  thf('35', plain, ($false), inference('demod', [status(thm)], ['24', '34'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
