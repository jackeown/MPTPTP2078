%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ydJFIigQ0z

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:37 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 127 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  563 (1749 expanded)
%              Number of equality atoms :   51 ( 186 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf('0',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X15 ) @ X15 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('17',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','29'])).

thf('31',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( sk_B
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','46','47'])).

thf('49',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('51',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ydJFIigQ0z
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.70  % Solved by: fo/fo7.sh
% 0.49/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.70  % done 275 iterations in 0.246s
% 0.49/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.70  % SZS output start Refutation
% 0.49/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.49/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.49/0.70  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.49/0.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.70  thf(t63_funct_1, conjecture,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.70       ( ![B:$i]:
% 0.49/0.70         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.70           ( ( ( v2_funct_1 @ A ) & 
% 0.49/0.70               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.49/0.70               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.49/0.70             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.70    (~( ![A:$i]:
% 0.49/0.70        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.70          ( ![B:$i]:
% 0.49/0.70            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.70              ( ( ( v2_funct_1 @ A ) & 
% 0.49/0.70                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.49/0.70                  ( ( k5_relat_1 @ A @ B ) =
% 0.49/0.70                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.49/0.70                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.49/0.70    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.49/0.70  thf('0', plain,
% 0.49/0.70      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(t37_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ A ) =>
% 0.49/0.70       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.49/0.70         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.49/0.70  thf('1', plain,
% 0.49/0.70      (![X1 : $i]:
% 0.49/0.70         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 0.49/0.70          | ~ (v1_relat_1 @ X1))),
% 0.49/0.70      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.49/0.70  thf(t80_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ A ) =>
% 0.49/0.70       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.49/0.70  thf('2', plain,
% 0.49/0.70      (![X9 : $i]:
% 0.49/0.70         (((k5_relat_1 @ X9 @ (k6_relat_1 @ (k2_relat_1 @ X9))) = (X9))
% 0.49/0.70          | ~ (v1_relat_1 @ X9))),
% 0.49/0.70      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.49/0.70  thf('3', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.49/0.70            = (k4_relat_1 @ X0))
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.49/0.70      inference('sup+', [status(thm)], ['1', '2'])).
% 0.49/0.70  thf(dt_k4_relat_1, axiom,
% 0.49/0.70    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.49/0.70  thf('4', plain,
% 0.49/0.70      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.70  thf('5', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.49/0.70              = (k4_relat_1 @ X0)))),
% 0.49/0.70      inference('clc', [status(thm)], ['3', '4'])).
% 0.49/0.70  thf('6', plain,
% 0.49/0.70      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.49/0.70          = (k4_relat_1 @ sk_A))
% 0.49/0.70        | ~ (v1_relat_1 @ sk_A))),
% 0.49/0.70      inference('sup+', [status(thm)], ['0', '5'])).
% 0.49/0.70  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('8', plain,
% 0.49/0.70      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.49/0.70         = (k4_relat_1 @ sk_A))),
% 0.49/0.70      inference('demod', [status(thm)], ['6', '7'])).
% 0.49/0.70  thf('9', plain,
% 0.49/0.70      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.70  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(d9_funct_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.70       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.49/0.70  thf('11', plain,
% 0.49/0.70      (![X10 : $i]:
% 0.49/0.70         (~ (v2_funct_1 @ X10)
% 0.49/0.70          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.49/0.70          | ~ (v1_funct_1 @ X10)
% 0.49/0.70          | ~ (v1_relat_1 @ X10))),
% 0.49/0.70      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.49/0.70  thf('12', plain,
% 0.49/0.70      ((~ (v1_funct_1 @ sk_A)
% 0.49/0.70        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.49/0.70        | ~ (v2_funct_1 @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.70  thf('13', plain, ((v1_funct_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('14', plain, ((v2_funct_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('15', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.49/0.70      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.49/0.70  thf(t61_funct_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.70       ( ( v2_funct_1 @ A ) =>
% 0.49/0.70         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.49/0.70             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.49/0.70           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.49/0.70             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.70  thf('16', plain,
% 0.49/0.70      (![X15 : $i]:
% 0.49/0.70         (~ (v2_funct_1 @ X15)
% 0.49/0.70          | ((k5_relat_1 @ (k2_funct_1 @ X15) @ X15)
% 0.49/0.70              = (k6_relat_1 @ (k2_relat_1 @ X15)))
% 0.49/0.70          | ~ (v1_funct_1 @ X15)
% 0.49/0.70          | ~ (v1_relat_1 @ X15))),
% 0.49/0.70      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.49/0.70  thf('17', plain,
% 0.49/0.70      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.49/0.70          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.49/0.70        | ~ (v1_relat_1 @ sk_A)
% 0.49/0.70        | ~ (v1_funct_1 @ sk_A)
% 0.49/0.70        | ~ (v2_funct_1 @ sk_A))),
% 0.49/0.70      inference('sup+', [status(thm)], ['15', '16'])).
% 0.49/0.70  thf('18', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('21', plain, ((v2_funct_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('22', plain,
% 0.49/0.70      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.49/0.70         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 0.49/0.70  thf(t55_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ A ) =>
% 0.49/0.70       ( ![B:$i]:
% 0.49/0.70         ( ( v1_relat_1 @ B ) =>
% 0.49/0.70           ( ![C:$i]:
% 0.49/0.70             ( ( v1_relat_1 @ C ) =>
% 0.49/0.70               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.49/0.70                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.49/0.70  thf('23', plain,
% 0.49/0.70      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X2)
% 0.49/0.70          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.49/0.70              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.49/0.70          | ~ (v1_relat_1 @ X4)
% 0.49/0.70          | ~ (v1_relat_1 @ X3))),
% 0.49/0.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.49/0.70  thf('24', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.49/0.70            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.49/0.70          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ sk_A))),
% 0.49/0.70      inference('sup+', [status(thm)], ['22', '23'])).
% 0.49/0.70  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('26', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.49/0.70            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.49/0.70          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.49/0.70          | ~ (v1_relat_1 @ X0))),
% 0.49/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.49/0.70  thf('27', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ sk_A)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.49/0.70              = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['9', '26'])).
% 0.49/0.70  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('29', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.49/0.70              = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 0.49/0.70      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.70  thf('30', plain,
% 0.49/0.70      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.49/0.70          = (k4_relat_1 @ sk_A))
% 0.49/0.70        | ~ (v1_relat_1 @ sk_B))),
% 0.49/0.70      inference('sup+', [status(thm)], ['8', '29'])).
% 0.49/0.70  thf('31', plain,
% 0.49/0.70      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(t71_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.49/0.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.49/0.70  thf('32', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.49/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.49/0.70  thf('33', plain,
% 0.49/0.70      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 0.49/0.70      inference('sup+', [status(thm)], ['31', '32'])).
% 0.49/0.70  thf(t27_funct_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.70       ( ![B:$i]:
% 0.49/0.70         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.70           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.49/0.70             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.70  thf('34', plain,
% 0.49/0.70      (![X13 : $i, X14 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X13)
% 0.49/0.70          | ~ (v1_funct_1 @ X13)
% 0.49/0.70          | (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X14))
% 0.49/0.70          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X14)) != (k1_relat_1 @ X13))
% 0.49/0.70          | ~ (v1_funct_1 @ X14)
% 0.49/0.70          | ~ (v1_relat_1 @ X14))),
% 0.49/0.70      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.49/0.70  thf('35', plain,
% 0.49/0.70      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.49/0.70        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.70        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.70        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.49/0.70        | ~ (v1_funct_1 @ sk_A)
% 0.49/0.70        | ~ (v1_relat_1 @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.70  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('38', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('39', plain, ((v1_funct_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('41', plain,
% 0.49/0.70      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.49/0.70        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['35', '36', '37', '38', '39', '40'])).
% 0.49/0.70  thf('42', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.49/0.70      inference('simplify', [status(thm)], ['41'])).
% 0.49/0.70  thf(t77_relat_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ B ) =>
% 0.49/0.70       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.49/0.70         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.49/0.70  thf('43', plain,
% 0.49/0.70      (![X7 : $i, X8 : $i]:
% 0.49/0.70         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.49/0.70          | ((k5_relat_1 @ (k6_relat_1 @ X8) @ X7) = (X7))
% 0.49/0.70          | ~ (v1_relat_1 @ X7))),
% 0.49/0.70      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.49/0.70  thf('44', plain,
% 0.49/0.70      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.70        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.49/0.70  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('46', plain,
% 0.49/0.70      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B))),
% 0.49/0.70      inference('demod', [status(thm)], ['44', '45'])).
% 0.49/0.70  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('48', plain, (((sk_B) = (k4_relat_1 @ sk_A))),
% 0.49/0.70      inference('demod', [status(thm)], ['30', '46', '47'])).
% 0.49/0.70  thf('49', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('50', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.49/0.70      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.49/0.70  thf('51', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.49/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.49/0.70  thf('52', plain, ($false),
% 0.49/0.70      inference('simplify_reflect-', [status(thm)], ['48', '51'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
