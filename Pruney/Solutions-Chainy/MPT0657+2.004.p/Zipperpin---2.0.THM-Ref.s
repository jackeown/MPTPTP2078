%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ufPY16YKYH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:40 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 418 expanded)
%              Number of leaves         :   19 ( 131 expanded)
%              Depth                    :   17
%              Number of atoms          :  629 (6397 expanded)
%              Number of equality atoms :   70 ( 714 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X14 ) @ X14 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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

thf('1',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_funct_1,axiom,(
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

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X15
        = ( k2_funct_1 @ X16 ) )
      | ( ( k5_relat_1 @ X16 @ X15 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k2_relat_1 @ sk_A )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X4 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ( ( k1_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','19'])).

thf('21',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('23',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X15
        = ( k2_funct_1 @ X16 ) )
      | ( ( k5_relat_1 @ X16 @ X15 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('25',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k2_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_A ) )
    | ( sk_A
      = ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('30',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33','34','35','36'])).

thf('38',plain,(
    v2_funct_1 @ sk_B ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','38','39','40','41'])).

thf('43',plain,
    ( sk_A
    = ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( sk_A
    = ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['42'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ( ( k1_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','43','44'])).

thf('46',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_B
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_B ),
    inference(simplify,[status(thm)],['37'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51'])).

thf('53',plain,
    ( sk_B
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( sk_A
    = ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['42'])).

thf('56',plain,(
    sk_B
 != ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ufPY16YKYH
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.62  % Solved by: fo/fo7.sh
% 0.35/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.62  % done 145 iterations in 0.159s
% 0.35/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.62  % SZS output start Refutation
% 0.35/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.35/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.62  thf(t61_funct_1, axiom,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.62       ( ( v2_funct_1 @ A ) =>
% 0.35/0.62         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.35/0.62             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.35/0.62           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.35/0.62             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.35/0.62  thf('0', plain,
% 0.35/0.62      (![X14 : $i]:
% 0.35/0.62         (~ (v2_funct_1 @ X14)
% 0.35/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X14) @ X14)
% 0.35/0.62              = (k6_relat_1 @ (k2_relat_1 @ X14)))
% 0.35/0.62          | ~ (v1_funct_1 @ X14)
% 0.35/0.62          | ~ (v1_relat_1 @ X14))),
% 0.35/0.62      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.35/0.62  thf(t64_funct_1, conjecture,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.62       ( ![B:$i]:
% 0.35/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.62           ( ( ( v2_funct_1 @ A ) & 
% 0.35/0.62               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.35/0.62               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.35/0.62             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.62    (~( ![A:$i]:
% 0.35/0.62        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.62          ( ![B:$i]:
% 0.35/0.62            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.62              ( ( ( v2_funct_1 @ A ) & 
% 0.35/0.62                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.35/0.62                  ( ( k5_relat_1 @ B @ A ) =
% 0.35/0.62                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.35/0.62                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.35/0.62    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.35/0.62  thf('1', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(t63_funct_1, axiom,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.62       ( ![B:$i]:
% 0.35/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.62           ( ( ( v2_funct_1 @ A ) & 
% 0.35/0.62               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.35/0.62               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.35/0.62             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.62  thf('2', plain,
% 0.35/0.62      (![X15 : $i, X16 : $i]:
% 0.35/0.62         (~ (v1_relat_1 @ X15)
% 0.35/0.62          | ~ (v1_funct_1 @ X15)
% 0.35/0.62          | ((X15) = (k2_funct_1 @ X16))
% 0.35/0.62          | ((k5_relat_1 @ X16 @ X15) != (k6_relat_1 @ (k1_relat_1 @ X16)))
% 0.35/0.62          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X15))
% 0.35/0.62          | ~ (v2_funct_1 @ X16)
% 0.35/0.62          | ~ (v1_funct_1 @ X16)
% 0.35/0.62          | ~ (v1_relat_1 @ X16))),
% 0.35/0.62      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.35/0.62  thf('3', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         (((k5_relat_1 @ sk_A @ X0) != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.35/0.62          | ~ (v1_relat_1 @ sk_A)
% 0.35/0.62          | ~ (v1_funct_1 @ sk_A)
% 0.35/0.62          | ~ (v2_funct_1 @ sk_A)
% 0.35/0.62          | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ X0))
% 0.35/0.62          | ((X0) = (k2_funct_1 @ sk_A))
% 0.35/0.62          | ~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_relat_1 @ X0))),
% 0.35/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.62  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('5', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('6', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(d10_xboole_0, axiom,
% 0.35/0.62    (![A:$i,B:$i]:
% 0.35/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.62  thf('7', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.35/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.62  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.35/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.62  thf('9', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(t46_relat_1, axiom,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( v1_relat_1 @ A ) =>
% 0.35/0.62       ( ![B:$i]:
% 0.35/0.62         ( ( v1_relat_1 @ B ) =>
% 0.35/0.62           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.62             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.35/0.62  thf('10', plain,
% 0.35/0.62      (![X3 : $i, X4 : $i]:
% 0.35/0.62         (~ (v1_relat_1 @ X3)
% 0.35/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3)) = (k1_relat_1 @ X4))
% 0.35/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X4) @ (k1_relat_1 @ X3))
% 0.35/0.62          | ~ (v1_relat_1 @ X4))),
% 0.35/0.62      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.35/0.62  thf('11', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B))
% 0.35/0.62          | ~ (v1_relat_1 @ X0)
% 0.35/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0))
% 0.35/0.62          | ~ (v1_relat_1 @ sk_A))),
% 0.35/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.62  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('13', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B))
% 0.35/0.62          | ~ (v1_relat_1 @ X0)
% 0.35/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0)))),
% 0.35/0.62      inference('demod', [status(thm)], ['11', '12'])).
% 0.35/0.62  thf('14', plain,
% 0.35/0.62      ((((k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) = (k1_relat_1 @ sk_B))
% 0.35/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.62      inference('sup-', [status(thm)], ['8', '13'])).
% 0.35/0.62  thf('15', plain,
% 0.35/0.62      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(t71_relat_1, axiom,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.35/0.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.35/0.62  thf('16', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.35/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.62  thf('17', plain,
% 0.35/0.62      (((k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_A))),
% 0.35/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.35/0.62  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('19', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.35/0.62      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.35/0.62  thf('20', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         (((k5_relat_1 @ sk_A @ X0) != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.35/0.62          | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.35/0.62          | ((X0) = (k2_funct_1 @ sk_A))
% 0.35/0.62          | ~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_relat_1 @ X0))),
% 0.35/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6', '19'])).
% 0.35/0.62  thf('21', plain,
% 0.35/0.62      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('22', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.35/0.62      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.35/0.62  thf('23', plain,
% 0.35/0.62      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.35/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.62  thf('24', plain,
% 0.35/0.62      (![X15 : $i, X16 : $i]:
% 0.35/0.62         (~ (v1_relat_1 @ X15)
% 0.35/0.62          | ~ (v1_funct_1 @ X15)
% 0.35/0.62          | ((X15) = (k2_funct_1 @ X16))
% 0.35/0.62          | ((k5_relat_1 @ X16 @ X15) != (k6_relat_1 @ (k1_relat_1 @ X16)))
% 0.35/0.62          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X15))
% 0.35/0.62          | ~ (v2_funct_1 @ X16)
% 0.35/0.62          | ~ (v1_funct_1 @ X16)
% 0.35/0.62          | ~ (v1_relat_1 @ X16))),
% 0.35/0.62      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.35/0.62  thf('25', plain,
% 0.35/0.62      ((((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.35/0.62          != (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.35/0.62        | ~ (v1_relat_1 @ sk_B)
% 0.35/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.35/0.62        | ~ (v2_funct_1 @ sk_B)
% 0.35/0.62        | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ sk_A))
% 0.35/0.62        | ((sk_A) = (k2_funct_1 @ sk_B))
% 0.35/0.62        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.62        | ~ (v1_relat_1 @ sk_A))),
% 0.35/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.62  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('28', plain,
% 0.35/0.62      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.35/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.62  thf(t48_funct_1, axiom,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.62       ( ![B:$i]:
% 0.35/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.62           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.35/0.62               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.62             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.62  thf('29', plain,
% 0.35/0.62      (![X9 : $i, X10 : $i]:
% 0.35/0.62         (~ (v1_relat_1 @ X9)
% 0.35/0.62          | ~ (v1_funct_1 @ X9)
% 0.35/0.62          | (v2_funct_1 @ X9)
% 0.35/0.62          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.35/0.62          | ~ (v2_funct_1 @ (k5_relat_1 @ X9 @ X10))
% 0.35/0.62          | ~ (v1_funct_1 @ X10)
% 0.35/0.62          | ~ (v1_relat_1 @ X10))),
% 0.35/0.62      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.35/0.62  thf('30', plain,
% 0.35/0.62      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.35/0.62        | ~ (v1_relat_1 @ sk_A)
% 0.35/0.62        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.62        | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ sk_A))
% 0.35/0.62        | (v2_funct_1 @ sk_B)
% 0.35/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.35/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.62  thf(fc4_funct_1, axiom,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.35/0.62       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.35/0.62  thf('31', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 0.35/0.62      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.35/0.62  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('33', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('34', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('37', plain,
% 0.35/0.62      ((((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)) | (v2_funct_1 @ sk_B))),
% 0.35/0.62      inference('demod', [status(thm)],
% 0.35/0.62                ['30', '31', '32', '33', '34', '35', '36'])).
% 0.35/0.62  thf('38', plain, ((v2_funct_1 @ sk_B)),
% 0.35/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.35/0.62  thf('39', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('42', plain,
% 0.35/0.62      ((((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.35/0.62          != (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.35/0.62        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B))
% 0.35/0.62        | ((sk_A) = (k2_funct_1 @ sk_B)))),
% 0.35/0.62      inference('demod', [status(thm)],
% 0.35/0.62                ['25', '26', '27', '38', '39', '40', '41'])).
% 0.35/0.62  thf('43', plain, (((sk_A) = (k2_funct_1 @ sk_B))),
% 0.35/0.62      inference('simplify', [status(thm)], ['42'])).
% 0.35/0.62  thf('44', plain, (((sk_A) = (k2_funct_1 @ sk_B))),
% 0.35/0.62      inference('simplify', [status(thm)], ['42'])).
% 0.35/0.62  thf('45', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.35/0.62            != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.35/0.62          | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.35/0.62          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.35/0.62          | ~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_relat_1 @ X0))),
% 0.35/0.62      inference('demod', [status(thm)], ['20', '43', '44'])).
% 0.35/0.62  thf('46', plain,
% 0.35/0.62      ((((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.35/0.62          != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.35/0.62        | ~ (v1_relat_1 @ sk_B)
% 0.35/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.35/0.62        | ~ (v2_funct_1 @ sk_B)
% 0.35/0.62        | ~ (v1_relat_1 @ sk_B)
% 0.35/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.35/0.62        | ((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.35/0.62        | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B)))),
% 0.35/0.62      inference('sup-', [status(thm)], ['0', '45'])).
% 0.35/0.62  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('49', plain, ((v2_funct_1 @ sk_B)),
% 0.35/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.35/0.62  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('52', plain,
% 0.35/0.62      ((((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.35/0.62          != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.35/0.62        | ((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.35/0.62        | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B)))),
% 0.35/0.62      inference('demod', [status(thm)], ['46', '47', '48', '49', '50', '51'])).
% 0.35/0.62  thf('53', plain, (((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.35/0.62      inference('simplify', [status(thm)], ['52'])).
% 0.35/0.62  thf('54', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('55', plain, (((sk_A) = (k2_funct_1 @ sk_B))),
% 0.35/0.62      inference('simplify', [status(thm)], ['42'])).
% 0.35/0.62  thf('56', plain, (((sk_B) != (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.35/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.35/0.62  thf('57', plain, ($false),
% 0.35/0.62      inference('simplify_reflect-', [status(thm)], ['53', '56'])).
% 0.35/0.62  
% 0.35/0.62  % SZS output end Refutation
% 0.35/0.62  
% 0.35/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
