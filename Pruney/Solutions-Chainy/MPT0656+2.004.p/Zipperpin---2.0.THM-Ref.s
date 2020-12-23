%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0yr3XMGIc0

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:36 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 151 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  594 (2072 expanded)
%              Number of equality atoms :   54 ( 222 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ X9 @ X8 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

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

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

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
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ X18 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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

thf('25',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

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
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','30','31'])).

thf('33',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','35'])).

thf('37',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('38',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('39',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

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

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46'])).

thf('48',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ( ( k7_relat_1 @ X10 @ X11 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_B
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','52','53'])).

thf('55',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('57',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0yr3XMGIc0
% 0.13/0.37  % Computer   : n011.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:02:12 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.47/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.63  % Solved by: fo/fo7.sh
% 0.47/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.63  % done 217 iterations in 0.154s
% 0.47/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.63  % SZS output start Refutation
% 0.47/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.63  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.63  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.47/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.63  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.63  thf(t94_relat_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ B ) =>
% 0.47/0.63       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.47/0.63  thf('0', plain,
% 0.47/0.63      (![X8 : $i, X9 : $i]:
% 0.47/0.63         (((k7_relat_1 @ X9 @ X8) = (k5_relat_1 @ (k6_relat_1 @ X8) @ X9))
% 0.47/0.63          | ~ (v1_relat_1 @ X9))),
% 0.47/0.63      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.47/0.63  thf(t63_funct_1, conjecture,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.63           ( ( ( v2_funct_1 @ A ) & 
% 0.47/0.63               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.47/0.63               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.47/0.63             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.63    (~( ![A:$i]:
% 0.47/0.63        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.63          ( ![B:$i]:
% 0.47/0.63            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.63              ( ( ( v2_funct_1 @ A ) & 
% 0.47/0.63                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.47/0.63                  ( ( k5_relat_1 @ A @ B ) =
% 0.47/0.63                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.47/0.63                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.47/0.63    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.47/0.63  thf('1', plain,
% 0.47/0.63      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(t37_relat_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ A ) =>
% 0.47/0.63       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.47/0.63         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.47/0.63  thf('2', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 0.47/0.63          | ~ (v1_relat_1 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.63  thf(t80_relat_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ A ) =>
% 0.47/0.63       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.47/0.63  thf('3', plain,
% 0.47/0.63      (![X7 : $i]:
% 0.47/0.63         (((k5_relat_1 @ X7 @ (k6_relat_1 @ (k2_relat_1 @ X7))) = (X7))
% 0.47/0.63          | ~ (v1_relat_1 @ X7))),
% 0.47/0.63      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.47/0.63  thf('4', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.47/0.63            = (k4_relat_1 @ X0))
% 0.47/0.63          | ~ (v1_relat_1 @ X0)
% 0.47/0.63          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['2', '3'])).
% 0.47/0.63  thf(dt_k4_relat_1, axiom,
% 0.47/0.63    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.47/0.63  thf('5', plain,
% 0.47/0.63      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.47/0.63  thf('6', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v1_relat_1 @ X0)
% 0.47/0.63          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.47/0.63              = (k4_relat_1 @ X0)))),
% 0.47/0.63      inference('clc', [status(thm)], ['4', '5'])).
% 0.47/0.63  thf('7', plain,
% 0.47/0.63      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.47/0.63          = (k4_relat_1 @ sk_A))
% 0.47/0.63        | ~ (v1_relat_1 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['1', '6'])).
% 0.47/0.63  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('9', plain,
% 0.47/0.63      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.47/0.63         = (k4_relat_1 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.63  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(d9_funct_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.63       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.47/0.63  thf('11', plain,
% 0.47/0.63      (![X12 : $i]:
% 0.47/0.63         (~ (v2_funct_1 @ X12)
% 0.47/0.63          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.47/0.63          | ~ (v1_funct_1 @ X12)
% 0.47/0.63          | ~ (v1_relat_1 @ X12))),
% 0.47/0.63      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.47/0.63  thf('12', plain,
% 0.47/0.63      ((~ (v1_funct_1 @ sk_A)
% 0.47/0.63        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.47/0.63        | ~ (v2_funct_1 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.63  thf('13', plain, ((v1_funct_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('14', plain, ((v2_funct_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('15', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.47/0.63  thf(t61_funct_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.63       ( ( v2_funct_1 @ A ) =>
% 0.47/0.63         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.47/0.63             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.47/0.63           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.47/0.63             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.63  thf('16', plain,
% 0.47/0.63      (![X18 : $i]:
% 0.47/0.63         (~ (v2_funct_1 @ X18)
% 0.47/0.63          | ((k5_relat_1 @ (k2_funct_1 @ X18) @ X18)
% 0.47/0.63              = (k6_relat_1 @ (k2_relat_1 @ X18)))
% 0.47/0.63          | ~ (v1_funct_1 @ X18)
% 0.47/0.63          | ~ (v1_relat_1 @ X18))),
% 0.47/0.63      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.47/0.63  thf('17', plain,
% 0.47/0.63      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.47/0.63          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.47/0.63        | ~ (v1_relat_1 @ sk_A)
% 0.47/0.63        | ~ (v1_funct_1 @ sk_A)
% 0.47/0.63        | ~ (v2_funct_1 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['15', '16'])).
% 0.47/0.63  thf('18', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('21', plain, ((v2_funct_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.47/0.63         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 0.47/0.63  thf(t55_relat_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ A ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( v1_relat_1 @ B ) =>
% 0.47/0.63           ( ![C:$i]:
% 0.47/0.63             ( ( v1_relat_1 @ C ) =>
% 0.47/0.63               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.47/0.63                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.47/0.63  thf('23', plain,
% 0.47/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.63         (~ (v1_relat_1 @ X2)
% 0.47/0.63          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.47/0.63              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.47/0.63          | ~ (v1_relat_1 @ X4)
% 0.47/0.63          | ~ (v1_relat_1 @ X3))),
% 0.47/0.63      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.47/0.63  thf('24', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.47/0.63            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.47/0.63          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.47/0.63          | ~ (v1_relat_1 @ X0)
% 0.47/0.63          | ~ (v1_relat_1 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['22', '23'])).
% 0.47/0.63  thf('25', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.47/0.63  thf(dt_k2_funct_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.63       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.63         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.47/0.63  thf('26', plain,
% 0.47/0.63      (![X13 : $i]:
% 0.47/0.63         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.47/0.63          | ~ (v1_funct_1 @ X13)
% 0.47/0.63          | ~ (v1_relat_1 @ X13))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.63  thf('27', plain,
% 0.47/0.63      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.47/0.63        | ~ (v1_relat_1 @ sk_A)
% 0.47/0.63        | ~ (v1_funct_1 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.47/0.63  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('29', plain, ((v1_funct_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('30', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.47/0.63  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('32', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.47/0.63            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.47/0.63          | ~ (v1_relat_1 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['24', '30', '31'])).
% 0.47/0.63  thf('33', plain,
% 0.47/0.63      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.47/0.63          = (k4_relat_1 @ sk_A))
% 0.47/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.63      inference('sup+', [status(thm)], ['9', '32'])).
% 0.47/0.63  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('35', plain,
% 0.47/0.63      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.47/0.63         = (k4_relat_1 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.63  thf('36', plain,
% 0.47/0.63      ((((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k4_relat_1 @ sk_A))
% 0.47/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.63      inference('sup+', [status(thm)], ['0', '35'])).
% 0.47/0.63  thf('37', plain,
% 0.47/0.63      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(t71_relat_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.63       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.63  thf('38', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.47/0.63      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.63  thf('39', plain,
% 0.47/0.63      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['37', '38'])).
% 0.47/0.63  thf(t27_funct_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.63           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.47/0.63             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.63  thf('40', plain,
% 0.47/0.63      (![X16 : $i, X17 : $i]:
% 0.47/0.63         (~ (v1_relat_1 @ X16)
% 0.47/0.63          | ~ (v1_funct_1 @ X16)
% 0.47/0.63          | (r1_tarski @ (k2_relat_1 @ X16) @ (k1_relat_1 @ X17))
% 0.47/0.63          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X17)) != (k1_relat_1 @ X16))
% 0.47/0.63          | ~ (v1_funct_1 @ X17)
% 0.47/0.63          | ~ (v1_relat_1 @ X17))),
% 0.47/0.63      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.47/0.63  thf('41', plain,
% 0.47/0.63      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.47/0.63        | ~ (v1_relat_1 @ sk_B)
% 0.47/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.47/0.63        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.47/0.63        | ~ (v1_funct_1 @ sk_A)
% 0.47/0.63        | ~ (v1_relat_1 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.63  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('44', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('47', plain,
% 0.47/0.63      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.47/0.63        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '46'])).
% 0.47/0.63  thf('48', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.47/0.63      inference('simplify', [status(thm)], ['47'])).
% 0.47/0.63  thf(t97_relat_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ B ) =>
% 0.47/0.63       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.47/0.63         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.47/0.63  thf('49', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i]:
% 0.47/0.63         (~ (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.47/0.63          | ((k7_relat_1 @ X10 @ X11) = (X10))
% 0.47/0.63          | ~ (v1_relat_1 @ X10))),
% 0.47/0.63      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.47/0.63  thf('50', plain,
% 0.47/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.47/0.63        | ((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.63  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('52', plain, (((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (sk_B))),
% 0.47/0.63      inference('demod', [status(thm)], ['50', '51'])).
% 0.47/0.63  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('54', plain, (((sk_B) = (k4_relat_1 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['36', '52', '53'])).
% 0.47/0.63  thf('55', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('56', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.47/0.63  thf('57', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['55', '56'])).
% 0.47/0.63  thf('58', plain, ($false),
% 0.47/0.63      inference('simplify_reflect-', [status(thm)], ['54', '57'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
