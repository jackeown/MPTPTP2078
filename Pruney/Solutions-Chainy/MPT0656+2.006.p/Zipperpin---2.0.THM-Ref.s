%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fLp6sKAI52

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:37 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 171 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  586 (2348 expanded)
%              Number of equality atoms :   53 ( 249 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('7',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
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

thf('19',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ X18 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('20',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X3 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('32',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16
       != ( k6_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('34',plain,(
    ! [X15: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
        = X15 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['32','37'])).

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

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('47',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X5 ) @ X4 )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_B
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','51','52'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fLp6sKAI52
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.44/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.68  % Solved by: fo/fo7.sh
% 0.44/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.68  % done 331 iterations in 0.213s
% 0.44/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.68  % SZS output start Refutation
% 0.44/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.44/0.68  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.44/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.44/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.44/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.44/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.68  thf(t63_funct_1, conjecture,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.68           ( ( ( v2_funct_1 @ A ) & 
% 0.44/0.68               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.44/0.68               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.44/0.68             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.44/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.68    (~( ![A:$i]:
% 0.44/0.68        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.68          ( ![B:$i]:
% 0.44/0.68            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.68              ( ( ( v2_funct_1 @ A ) & 
% 0.44/0.68                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.44/0.68                  ( ( k5_relat_1 @ A @ B ) =
% 0.44/0.68                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.44/0.68                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.44/0.68    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.44/0.68  thf('0', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(d9_funct_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.68       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.44/0.68  thf('1', plain,
% 0.44/0.68      (![X7 : $i]:
% 0.44/0.68         (~ (v2_funct_1 @ X7)
% 0.44/0.68          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 0.44/0.68          | ~ (v1_funct_1 @ X7)
% 0.44/0.68          | ~ (v1_relat_1 @ X7))),
% 0.44/0.68      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.44/0.68  thf('2', plain,
% 0.44/0.68      ((~ (v1_funct_1 @ sk_A)
% 0.44/0.68        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.44/0.68        | ~ (v2_funct_1 @ sk_A))),
% 0.44/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.68  thf('3', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('4', plain, ((v2_funct_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('5', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.44/0.68  thf(dt_k2_funct_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.68       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.44/0.68         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.44/0.68  thf('6', plain,
% 0.44/0.68      (![X8 : $i]:
% 0.44/0.68         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.44/0.68          | ~ (v1_funct_1 @ X8)
% 0.44/0.68          | ~ (v1_relat_1 @ X8))),
% 0.44/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.44/0.68  thf('7', plain,
% 0.44/0.68      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.44/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.44/0.68        | ~ (v1_funct_1 @ sk_A))),
% 0.44/0.68      inference('sup+', [status(thm)], ['5', '6'])).
% 0.44/0.68  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('9', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('10', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.44/0.68  thf(t37_relat_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( v1_relat_1 @ A ) =>
% 0.44/0.68       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.44/0.68         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.44/0.68  thf('11', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.44/0.68          | ~ (v1_relat_1 @ X0))),
% 0.44/0.68      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.44/0.68  thf(t80_relat_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( v1_relat_1 @ A ) =>
% 0.44/0.68       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.44/0.68  thf('12', plain,
% 0.44/0.68      (![X6 : $i]:
% 0.44/0.68         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 0.44/0.68          | ~ (v1_relat_1 @ X6))),
% 0.44/0.68      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.44/0.68  thf('13', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.44/0.68            = (k4_relat_1 @ X0))
% 0.44/0.68          | ~ (v1_relat_1 @ X0)
% 0.44/0.68          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.44/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.44/0.68  thf('14', plain,
% 0.44/0.68      ((~ (v1_relat_1 @ sk_A)
% 0.44/0.68        | ((k5_relat_1 @ (k4_relat_1 @ sk_A) @ 
% 0.44/0.68            (k6_relat_1 @ (k1_relat_1 @ sk_A))) = (k4_relat_1 @ sk_A)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['10', '13'])).
% 0.44/0.68  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('16', plain,
% 0.44/0.68      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('17', plain,
% 0.44/0.68      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.44/0.68         = (k4_relat_1 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.44/0.68  thf('18', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.44/0.68  thf(t61_funct_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.68       ( ( v2_funct_1 @ A ) =>
% 0.44/0.68         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.44/0.68             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.44/0.68           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.44/0.68             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.44/0.68  thf('19', plain,
% 0.44/0.68      (![X18 : $i]:
% 0.44/0.68         (~ (v2_funct_1 @ X18)
% 0.44/0.68          | ((k5_relat_1 @ (k2_funct_1 @ X18) @ X18)
% 0.44/0.68              = (k6_relat_1 @ (k2_relat_1 @ X18)))
% 0.44/0.68          | ~ (v1_funct_1 @ X18)
% 0.44/0.68          | ~ (v1_relat_1 @ X18))),
% 0.44/0.68      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.44/0.68  thf('20', plain,
% 0.44/0.68      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.44/0.68          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.44/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.44/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.44/0.68        | ~ (v2_funct_1 @ sk_A))),
% 0.44/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.68  thf('21', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('23', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('24', plain, ((v2_funct_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('25', plain,
% 0.44/0.68      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.44/0.68         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.44/0.68      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.44/0.68  thf(t55_relat_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( v1_relat_1 @ A ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( v1_relat_1 @ B ) =>
% 0.44/0.68           ( ![C:$i]:
% 0.44/0.68             ( ( v1_relat_1 @ C ) =>
% 0.44/0.68               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.44/0.68                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.44/0.68  thf('26', plain,
% 0.44/0.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.68         (~ (v1_relat_1 @ X1)
% 0.44/0.68          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X3)
% 0.44/0.68              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X3)))
% 0.44/0.68          | ~ (v1_relat_1 @ X3)
% 0.44/0.68          | ~ (v1_relat_1 @ X2))),
% 0.44/0.68      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.44/0.68  thf('27', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.44/0.68            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.44/0.68          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.44/0.68          | ~ (v1_relat_1 @ X0)
% 0.44/0.68          | ~ (v1_relat_1 @ sk_A))),
% 0.44/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.44/0.68  thf('28', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.44/0.68  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('30', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.44/0.68            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.44/0.68          | ~ (v1_relat_1 @ X0))),
% 0.44/0.68      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.44/0.68  thf('31', plain,
% 0.44/0.68      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.44/0.68          = (k4_relat_1 @ sk_A))
% 0.44/0.68        | ~ (v1_relat_1 @ sk_B))),
% 0.44/0.68      inference('sup+', [status(thm)], ['17', '30'])).
% 0.44/0.68  thf('32', plain,
% 0.44/0.68      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(t34_funct_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.68       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.44/0.68         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.44/0.68           ( ![C:$i]:
% 0.44/0.68             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.44/0.68  thf('33', plain,
% 0.44/0.68      (![X15 : $i, X16 : $i]:
% 0.44/0.68         (((X16) != (k6_relat_1 @ X15))
% 0.44/0.68          | ((k1_relat_1 @ X16) = (X15))
% 0.44/0.68          | ~ (v1_funct_1 @ X16)
% 0.44/0.68          | ~ (v1_relat_1 @ X16))),
% 0.44/0.68      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.44/0.68  thf('34', plain,
% 0.44/0.68      (![X15 : $i]:
% 0.44/0.68         (~ (v1_relat_1 @ (k6_relat_1 @ X15))
% 0.44/0.68          | ~ (v1_funct_1 @ (k6_relat_1 @ X15))
% 0.44/0.68          | ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15)))),
% 0.44/0.68      inference('simplify', [status(thm)], ['33'])).
% 0.44/0.68  thf(fc3_funct_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.44/0.68       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.44/0.68  thf('35', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.44/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.44/0.68  thf('36', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.44/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.44/0.68  thf('37', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.44/0.68      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.44/0.68  thf('38', plain,
% 0.44/0.68      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 0.44/0.68      inference('sup+', [status(thm)], ['32', '37'])).
% 0.44/0.68  thf(t27_funct_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.68           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.44/0.68             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.44/0.68  thf('39', plain,
% 0.44/0.68      (![X13 : $i, X14 : $i]:
% 0.44/0.68         (~ (v1_relat_1 @ X13)
% 0.44/0.68          | ~ (v1_funct_1 @ X13)
% 0.44/0.68          | (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X14))
% 0.44/0.68          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X14)) != (k1_relat_1 @ X13))
% 0.44/0.68          | ~ (v1_funct_1 @ X14)
% 0.44/0.68          | ~ (v1_relat_1 @ X14))),
% 0.44/0.68      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.44/0.68  thf('40', plain,
% 0.44/0.68      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.44/0.68        | ~ (v1_relat_1 @ sk_B)
% 0.44/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.68        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.44/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.44/0.68        | ~ (v1_relat_1 @ sk_A))),
% 0.44/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.44/0.68  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('43', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('44', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('46', plain,
% 0.44/0.68      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.44/0.68        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.44/0.68      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 0.44/0.68  thf('47', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.44/0.68      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.68  thf(t77_relat_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( v1_relat_1 @ B ) =>
% 0.44/0.68       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.44/0.68         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.44/0.68  thf('48', plain,
% 0.44/0.68      (![X4 : $i, X5 : $i]:
% 0.44/0.68         (~ (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 0.44/0.68          | ((k5_relat_1 @ (k6_relat_1 @ X5) @ X4) = (X4))
% 0.44/0.68          | ~ (v1_relat_1 @ X4))),
% 0.44/0.68      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.44/0.68  thf('49', plain,
% 0.44/0.68      ((~ (v1_relat_1 @ sk_B)
% 0.44/0.68        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.68  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('51', plain,
% 0.44/0.68      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['49', '50'])).
% 0.44/0.68  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('53', plain, (((sk_B) = (k4_relat_1 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['31', '51', '52'])).
% 0.44/0.68  thf('54', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('55', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.44/0.68  thf('56', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['54', '55'])).
% 0.44/0.68  thf('57', plain, ($false),
% 0.44/0.68      inference('simplify_reflect-', [status(thm)], ['53', '56'])).
% 0.44/0.68  
% 0.44/0.68  % SZS output end Refutation
% 0.44/0.68  
% 0.44/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
