%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hfyc4Q7zQs

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 114 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  514 (1680 expanded)
%              Number of equality atoms :   50 ( 182 expanded)
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

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('7',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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

thf('11',plain,(
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

thf('12',plain,(
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
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k2_funct_1 @ X0 )
        = X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k2_funct_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('23',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('30',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19','20','27','32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_A )
      = sk_B )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(eq_res,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k2_funct_1 @ sk_A )
      = sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_funct_1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hfyc4Q7zQs
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 41 iterations in 0.040s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.50  thf(t64_funct_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50           ( ( ( v2_funct_1 @ A ) & 
% 0.22/0.50               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.22/0.50               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.22/0.50             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50              ( ( ( v2_funct_1 @ A ) & 
% 0.22/0.50                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.22/0.50                  ( ( k5_relat_1 @ B @ A ) =
% 0.22/0.50                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.22/0.50                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.22/0.50  thf('0', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d9_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X2 : $i]:
% 0.22/0.50         (~ (v2_funct_1 @ X2)
% 0.22/0.50          | ((k2_funct_1 @ X2) = (k4_relat_1 @ X2))
% 0.22/0.50          | ~ (v1_funct_1 @ X2)
% 0.22/0.50          | ~ (v1_relat_1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ sk_A)
% 0.22/0.50        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.22/0.50        | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('5', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.22/0.50  thf(t37_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.22/0.50         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X1 : $i]:
% 0.22/0.50         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 0.22/0.50          | ~ (v1_relat_1 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('9', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf(t61_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ( v2_funct_1 @ A ) =>
% 0.22/0.50         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.22/0.50             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.22/0.50           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.22/0.50             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         (~ (v2_funct_1 @ X8)
% 0.22/0.50          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.22/0.50              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.22/0.50          | ~ (v1_funct_1 @ X8)
% 0.22/0.50          | ~ (v1_relat_1 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.22/0.50  thf(l72_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50           ( ![D:$i]:
% 0.22/0.50             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.22/0.50               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.50                   ( ( k5_relat_1 @ B @ C ) =
% 0.22/0.50                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.22/0.50                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.22/0.50                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X4)
% 0.22/0.50          | ~ (v1_funct_1 @ X4)
% 0.22/0.50          | ((k2_relat_1 @ X6) != (X5))
% 0.22/0.50          | ((k5_relat_1 @ X6 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.22/0.50          | ((k5_relat_1 @ X4 @ X7) != (k6_relat_1 @ X5))
% 0.22/0.50          | ((X7) = (X6))
% 0.22/0.50          | ~ (v1_funct_1 @ X7)
% 0.22/0.50          | ~ (v1_relat_1 @ X7)
% 0.22/0.50          | ~ (v1_funct_1 @ X6)
% 0.22/0.50          | ~ (v1_relat_1 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [l72_funct_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X6)
% 0.22/0.50          | ~ (v1_funct_1 @ X6)
% 0.22/0.50          | ~ (v1_relat_1 @ X7)
% 0.22/0.50          | ~ (v1_funct_1 @ X7)
% 0.22/0.50          | ((X7) = (X6))
% 0.22/0.50          | ((k5_relat_1 @ X4 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.22/0.50          | ((k5_relat_1 @ X6 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.22/0.50          | ~ (v1_funct_1 @ X4)
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ((k5_relat_1 @ X1 @ X0)
% 0.22/0.50              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.22/0.50          | ((k2_funct_1 @ X0) = (X1))
% 0.22/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.50          | ((k2_funct_1 @ X0) = (X1))
% 0.22/0.50          | ((k5_relat_1 @ X1 @ X0)
% 0.22/0.50              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.22/0.50          | ~ (v2_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.22/0.50              != (k6_relat_1 @ (k2_relat_1 @ X1))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k5_relat_1 @ X0 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.22/0.50          | ((k6_relat_1 @ (k1_relat_1 @ sk_A))
% 0.22/0.50              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.22/0.50          | ~ (v1_relat_1 @ sk_A)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_A)
% 0.22/0.50          | ~ (v2_funct_1 @ sk_A)
% 0.22/0.50          | ((k2_funct_1 @ sk_A) = (X0))
% 0.22/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.22/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('21', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.22/0.50  thf(fc5_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.22/0.50       ( ( v1_relat_1 @ ( k4_relat_1 @ A ) ) & 
% 0.22/0.50         ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X3 : $i]:
% 0.22/0.50         ((v1_funct_1 @ (k4_relat_1 @ X3))
% 0.22/0.50          | ~ (v2_funct_1 @ X3)
% 0.22/0.50          | ~ (v1_funct_1 @ X3)
% 0.22/0.50          | ~ (v1_relat_1 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (((v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ sk_A)
% 0.22/0.50        | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('26', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.22/0.50  thf('28', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.22/0.50  thf(dt_k4_relat_1, axiom,
% 0.22/0.50    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (((v1_relat_1 @ (k2_funct_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.50      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.22/0.50          | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.22/0.50              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.22/0.50          | ((k2_funct_1 @ sk_A) = (X0))
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['15', '16', '17', '18', '19', '20', '27', '32'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.50        | ((k2_funct_1 @ sk_A) = (sk_B))
% 0.22/0.50        | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.22/0.50            != (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.22/0.50      inference('eq_res', [status(thm)], ['33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((((k2_funct_1 @ sk_A) = (sk_B))
% 0.22/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.50  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('38', plain, (((k2_funct_1 @ sk_A) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.50  thf('39', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('40', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
