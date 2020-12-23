%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nVfWh2uko5

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 212 expanded)
%              Number of leaves         :   23 (  73 expanded)
%              Depth                    :   24
%              Number of atoms          :  571 (1839 expanded)
%              Number of equality atoms :   32 ( 125 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X15 ) )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X15: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X15 ) )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('3',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( X14
        = ( k1_wellord1 @ ( k1_wellord2 @ X13 ) @ X14 ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9
       != ( k1_wellord2 @ X8 ) )
      | ( ( k3_relat_1 @ X9 )
        = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('9',plain,(
    ! [X8: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X8 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X8 ) )
        = X8 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t13_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X2 @ X3 ) @ ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t13_wellord1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X17 ) @ X16 )
        = ( k1_wellord2 @ X16 ) )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      = ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_wellord1 @ X6 )
      | ~ ( r4_wellord1 @ X6 @ ( k2_wellord1 @ X6 @ ( k1_wellord1 @ X6 @ X7 ) ) )
      | ~ ( r2_hidden @ X7 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X8: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( X14
        = ( k1_wellord1 @ ( k1_wellord2 @ X13 ) @ X14 ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('41',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('46',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r4_wellord1 @ X4 @ X5 )
      | ~ ( r4_wellord1 @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('51',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('52',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('54',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','52','53'])).

thf('55',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','54'])).

thf('56',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nVfWh2uko5
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 43 iterations in 0.048s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.50  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.20/0.50  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.50  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.50  thf(t7_wellord2, axiom,
% 0.20/0.50    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X15 : $i]:
% 0.20/0.50         ((v2_wellord1 @ (k1_wellord2 @ X15)) | ~ (v3_ordinal1 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.50  thf(t24_ordinal1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.50           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.20/0.50                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v3_ordinal1 @ X0)
% 0.20/0.50          | (r2_hidden @ X1 @ X0)
% 0.20/0.50          | ((X1) = (X0))
% 0.20/0.50          | (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X15 : $i]:
% 0.20/0.50         ((v2_wellord1 @ (k1_wellord2 @ X15)) | ~ (v3_ordinal1 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.50  thf(t11_wellord2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.50           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.50             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.50              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.50                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v3_ordinal1 @ X0)
% 0.20/0.50          | (r2_hidden @ X1 @ X0)
% 0.20/0.50          | ((X1) = (X0))
% 0.20/0.50          | (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.50  thf(t10_wellord2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.50           ( ( r2_hidden @ A @ B ) =>
% 0.20/0.50             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         (~ (v3_ordinal1 @ X13)
% 0.20/0.50          | ((X14) = (k1_wellord1 @ (k1_wellord2 @ X13) @ X14))
% 0.20/0.50          | ~ (r2_hidden @ X14 @ X13)
% 0.20/0.50          | ~ (v3_ordinal1 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v3_ordinal1 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ((X1) = (X0))
% 0.20/0.50          | ~ (v3_ordinal1 @ X0)
% 0.20/0.50          | ~ (v3_ordinal1 @ X1)
% 0.20/0.50          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.50          | ~ (v3_ordinal1 @ X0)
% 0.20/0.50          | ((X1) = (X0))
% 0.20/0.50          | (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.50  thf(d1_wellord2, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.20/0.50         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.50           ( ![C:$i,D:$i]:
% 0.20/0.50             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.50               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.50                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (((X9) != (k1_wellord2 @ X8))
% 0.20/0.50          | ((k3_relat_1 @ X9) = (X8))
% 0.20/0.50          | ~ (v1_relat_1 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X8 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (k1_wellord2 @ X8))
% 0.20/0.50          | ((k3_relat_1 @ (k1_wellord2 @ X8)) = (X8)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.50  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.50  thf('10', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.50  thf('11', plain, (![X8 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X8)) = (X8))),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf(t13_wellord1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_wellord1 @ X2 @ X3) @ (k3_relat_1 @ X2))
% 0.20/0.50          | ~ (v1_relat_1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t13_wellord1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf(t8_wellord2, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.50       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (((k2_wellord1 @ (k1_wellord2 @ X17) @ X16) = (k1_wellord2 @ X16))
% 0.20/0.50          | ~ (r1_tarski @ X16 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k2_wellord1 @ (k1_wellord2 @ X0) @ 
% 0.20/0.50           (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.50           = (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf(t57_wellord1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( v2_wellord1 @ A ) =>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.50                ( r4_wellord1 @
% 0.20/0.50                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (v2_wellord1 @ X6)
% 0.20/0.50          | ~ (r4_wellord1 @ X6 @ (k2_wellord1 @ X6 @ (k1_wellord1 @ X6 @ X7)))
% 0.20/0.50          | ~ (r2_hidden @ X7 @ (k3_relat_1 @ X6))
% 0.20/0.50          | ~ (v1_relat_1 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.50             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.20/0.50          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.50  thf('21', plain, (![X8 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X8)) = (X8))),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.50             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.20/0.50          | ~ (v3_ordinal1 @ X0)
% 0.20/0.50          | (r2_hidden @ X1 @ X0)
% 0.20/0.50          | ((X0) = (X1))
% 0.20/0.50          | ~ (v3_ordinal1 @ X1)
% 0.20/0.50          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.50        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.50        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.50        | ((sk_B) = (sk_A))
% 0.20/0.50        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.50        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '23'])).
% 0.20/0.50  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.50        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.50        | ((sk_B) = (sk_A))
% 0.20/0.50        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.50  thf('28', plain, (((sk_A) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.50        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.50        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.50        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.50        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '29'])).
% 0.20/0.50  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain, (((r2_hidden @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((~ (v3_ordinal1 @ sk_B)
% 0.20/0.50        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.50        | ((sk_B) = (sk_A))
% 0.20/0.50        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.50        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '32'])).
% 0.20/0.50  thf('34', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((r2_hidden @ sk_A @ sk_B)
% 0.20/0.50        | ((sk_B) = (sk_A))
% 0.20/0.50        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.50  thf('37', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.50  thf('38', plain, (((sk_A) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         (~ (v3_ordinal1 @ X13)
% 0.20/0.50          | ((X14) = (k1_wellord1 @ (k1_wellord2 @ X13) @ X14))
% 0.20/0.50          | ~ (r2_hidden @ X14 @ X13)
% 0.20/0.50          | ~ (v3_ordinal1 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.50        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.20/0.50        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('44', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.50             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.20/0.50        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.50        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t50_wellord1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v1_relat_1 @ B ) =>
% 0.20/0.50           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X4)
% 0.20/0.50          | (r4_wellord1 @ X4 @ X5)
% 0.20/0.50          | ~ (r4_wellord1 @ X5 @ X4)
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.20/0.50        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.50  thf('51', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.50  thf('53', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('54', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '52', '53'])).
% 0.20/0.50  thf('55', plain, (~ (v3_ordinal1 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '54'])).
% 0.20/0.50  thf('56', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain, ($false), inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
