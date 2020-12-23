%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QaFSsSxV5g

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:41 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 207 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  566 (2930 expanded)
%              Number of equality atoms :   51 ( 313 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) ) @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('14',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','23','24','30'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ ( k6_relat_1 @ X11 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('37',plain,(
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

thf('38',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k4_relat_1 @ sk_A ) )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k4_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('46',plain,
    ( ( ( k4_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k4_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('52',plain,
    ( ( k4_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_relat_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['35','52'])).

thf('54',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('56',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QaFSsSxV5g
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:15:48 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 102 iterations in 0.073s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.36/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.54  thf(t64_funct_1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.54           ( ( ( v2_funct_1 @ A ) & 
% 0.36/0.54               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.36/0.54               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.36/0.54             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.54              ( ( ( v2_funct_1 @ A ) & 
% 0.36/0.54                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.36/0.54                  ( ( k5_relat_1 @ B @ A ) =
% 0.36/0.54                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.36/0.54                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.36/0.54  thf('0', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d9_funct_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X12 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X12)
% 0.36/0.54          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.36/0.54          | ~ (v1_funct_1 @ X12)
% 0.36/0.54          | ~ (v1_relat_1 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      ((~ (v1_funct_1 @ sk_A)
% 0.36/0.54        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.36/0.54        | ~ (v2_funct_1 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf('3', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('4', plain, ((v2_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('5', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.36/0.54  thf(t61_funct_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54       ( ( v2_funct_1 @ A ) =>
% 0.36/0.54         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.36/0.54             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.36/0.54           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.36/0.54             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X15 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X15)
% 0.36/0.54          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15))
% 0.36/0.54              = (k6_relat_1 @ (k1_relat_1 @ X15)))
% 0.36/0.54          | ~ (v1_funct_1 @ X15)
% 0.36/0.54          | ~ (v1_relat_1 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      ((((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.36/0.54          = (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_A)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_A)
% 0.36/0.54        | ~ (v2_funct_1 @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.54  thf('8', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('10', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('11', plain, ((v2_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.36/0.54         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.36/0.54  thf(t45_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( v1_relat_1 @ B ) =>
% 0.36/0.54           ( r1_tarski @
% 0.36/0.54             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X2)
% 0.36/0.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X3 @ X2)) @ 
% 0.36/0.54             (k2_relat_1 @ X2))
% 0.36/0.54          | ~ (v1_relat_1 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (((r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) @ 
% 0.36/0.54         (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_A)
% 0.36/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf(t71_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.36/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.36/0.54  thf('15', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.36/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.54  thf('16', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.36/0.54  thf(t55_funct_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54       ( ( v2_funct_1 @ A ) =>
% 0.36/0.54         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.36/0.54           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X14 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X14)
% 0.36/0.54          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 0.36/0.54          | ~ (v1_funct_1 @ X14)
% 0.36/0.54          | ~ (v1_relat_1 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_A)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_A)
% 0.36/0.54        | ~ (v2_funct_1 @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('21', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('22', plain, ((v2_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (((k2_relat_1 @ sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.36/0.54  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('25', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.36/0.54  thf(dt_k2_funct_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.36/0.54         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X13 : $i]:
% 0.36/0.54         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.36/0.54          | ~ (v1_funct_1 @ X13)
% 0.36/0.54          | ~ (v1_relat_1 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_A)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['25', '26'])).
% 0.36/0.54  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('29', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('30', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.36/0.54  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['14', '15', '23', '24', '30'])).
% 0.36/0.54  thf(t79_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ B ) =>
% 0.36/0.54       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.36/0.54         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i]:
% 0.36/0.54         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.36/0.54          | ((k5_relat_1 @ X10 @ (k6_relat_1 @ X11)) = (X10))
% 0.36/0.54          | ~ (v1_relat_1 @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.54        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) = (sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.54  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) = (sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t37_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.36/0.54         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X1 : $i]:
% 0.36/0.54         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 0.36/0.54          | ~ (v1_relat_1 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.36/0.54  thf(t78_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X9 : $i]:
% 0.36/0.54         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X9)) @ X9) = (X9))
% 0.36/0.54          | ~ (v1_relat_1 @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 0.36/0.54            = (k4_relat_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.54  thf(dt_k4_relat_1, axiom,
% 0.36/0.54    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 0.36/0.54              = (k4_relat_1 @ X0)))),
% 0.36/0.54      inference('clc', [status(thm)], ['39', '40'])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      ((((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ (k4_relat_1 @ sk_A))
% 0.36/0.54          = (k4_relat_1 @ sk_A))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['36', '41'])).
% 0.36/0.54  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ (k4_relat_1 @ sk_A))
% 0.36/0.54         = (k4_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.54  thf(t55_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( v1_relat_1 @ B ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( v1_relat_1 @ C ) =>
% 0.36/0.54               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.36/0.54                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X4)
% 0.36/0.54          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 0.36/0.54              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 0.36/0.54          | ~ (v1_relat_1 @ X6)
% 0.36/0.54          | ~ (v1_relat_1 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      ((((k4_relat_1 @ sk_A)
% 0.36/0.54          = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_B)
% 0.36/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['44', '45'])).
% 0.36/0.54  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('48', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.36/0.54  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      (((k4_relat_1 @ sk_A)
% 0.36/0.54         = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.36/0.54         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      (((k4_relat_1 @ sk_A)
% 0.36/0.54         = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.36/0.54      inference('demod', [status(thm)], ['50', '51'])).
% 0.36/0.54  thf('53', plain, (((k4_relat_1 @ sk_A) = (sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['35', '52'])).
% 0.36/0.54  thf('54', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('55', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.36/0.54  thf('56', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.54  thf('57', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['53', '56'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
