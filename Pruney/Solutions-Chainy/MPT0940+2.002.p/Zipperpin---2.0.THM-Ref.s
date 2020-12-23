%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SMQMmkij4z

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 120 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  617 (1146 expanded)
%              Number of equality atoms :   17 (  45 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t5_wellord2,conjecture,(
    ! [A: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( v4_relat_2 @ ( k1_wellord2 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t5_wellord2])).

thf('0',plain,(
    ~ ( v4_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
       != ( k1_wellord2 @ X9 ) )
      | ( ( k3_relat_1 @ X10 )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X9: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X9 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X9 ) )
        = X9 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l3_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) )
           => ( B = C ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X6 ) @ ( sk_C @ X6 ) ) @ X6 )
      | ( v4_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 )
      | ( r2_hidden @ X4 @ ( k3_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 ) @ ( sk_B @ X6 ) ) @ X6 )
      | ( v4_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10
       != ( k1_wellord2 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('14',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ ( k1_wellord2 @ X9 ) )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X11 @ X9 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('16',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ ( k1_wellord2 @ X9 ) )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X11 @ X9 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('23',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 ) @ ( sk_B @ X6 ) ) @ X6 )
      | ( v4_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 )
      | ( r2_hidden @ X4 @ ( k3_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X6 ) @ ( sk_C @ X6 ) ) @ X6 )
      | ( v4_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('33',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ ( k1_wellord2 @ X9 ) )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X11 @ X9 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( ( sk_C @ ( k1_wellord2 @ X0 ) )
        = ( sk_B @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( ( sk_C @ ( k1_wellord2 @ X0 ) )
        = ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k1_wellord2 @ X0 ) )
        = ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X6: $i] :
      ( ( ( sk_B @ X6 )
       != ( sk_C @ X6 ) )
      | ( v4_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_wellord2 @ X0 ) )
       != ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_wellord2 @ X0 ) )
       != ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SMQMmkij4z
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 37 iterations in 0.031s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.49  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(t5_wellord2, conjecture, (![A:$i]: ( v4_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]: ( v4_relat_2 @ ( k1_wellord2 @ A ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t5_wellord2])).
% 0.21/0.49  thf('0', plain, (~ (v4_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d1_wellord2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.49         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.49           ( ![C:$i,D:$i]:
% 0.21/0.49             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.49               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.49                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (((X10) != (k1_wellord2 @ X9))
% 0.21/0.49          | ((k3_relat_1 @ X10) = (X9))
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X9 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X9))
% 0.21/0.49          | ((k3_relat_1 @ (k1_wellord2 @ X9)) = (X9)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.49  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.49  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('4', plain, (![X9 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X9)) = (X9))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(l3_wellord1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( v4_relat_2 @ A ) <=>
% 0.21/0.49         ( ![B:$i,C:$i]:
% 0.21/0.49           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 0.21/0.49               ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) =>
% 0.21/0.49             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ (sk_B @ X6) @ (sk_C @ X6)) @ X6)
% 0.21/0.49          | (v4_relat_2 @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_wellord1])).
% 0.21/0.49  thf(t30_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ C ) =>
% 0.21/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.49         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.49           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5)
% 0.21/0.49          | (r2_hidden @ X4 @ (k3_relat_1 @ X5))
% 0.21/0.49          | ~ (v1_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r2_hidden @ (sk_C @ X0) @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.49          | (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['4', '8'])).
% 0.21/0.49  thf('10', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ (sk_C @ X6) @ (sk_B @ X6)) @ X6)
% 0.21/0.49          | (v4_relat_2 @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_wellord1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (((X10) != (k1_wellord2 @ X9))
% 0.21/0.49          | ~ (r2_hidden @ X11 @ X9)
% 0.21/0.49          | ~ (r2_hidden @ X12 @ X9)
% 0.21/0.49          | (r1_tarski @ X11 @ X12)
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X9))
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ (k1_wellord2 @ X9))
% 0.21/0.49          | (r1_tarski @ X11 @ X12)
% 0.21/0.49          | ~ (r2_hidden @ X12 @ X9)
% 0.21/0.49          | ~ (r2_hidden @ X11 @ X9))),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ (k1_wellord2 @ X9))
% 0.21/0.49          | (r1_tarski @ X11 @ X12)
% 0.21/0.49          | ~ (r2_hidden @ X12 @ X9)
% 0.21/0.49          | ~ (r2_hidden @ X11 @ X9))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | ~ (r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_B @ (k1_wellord2 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '16'])).
% 0.21/0.49  thf('18', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | ~ (r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_B @ (k1_wellord2 @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_B @ (k1_wellord2 @ X0)))
% 0.21/0.49          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_B @ (k1_wellord2 @ X0)))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.49  thf('22', plain, (![X9 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X9)) = (X9))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ (sk_C @ X6) @ (sk_B @ X6)) @ X6)
% 0.21/0.49          | (v4_relat_2 @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_wellord1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5)
% 0.21/0.49          | (r2_hidden @ X4 @ (k3_relat_1 @ X5))
% 0.21/0.49          | ~ (v1_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r2_hidden @ (sk_B @ X0) @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.49          | (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['22', '26'])).
% 0.21/0.49  thf('28', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_B @ (k1_wellord2 @ X0))))),
% 0.21/0.49      inference('clc', [status(thm)], ['21', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ (sk_B @ X6) @ (sk_C @ X6)) @ X6)
% 0.21/0.49          | (v4_relat_2 @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_wellord1])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ (k1_wellord2 @ X9))
% 0.21/0.49          | (r1_tarski @ X11 @ X12)
% 0.21/0.49          | ~ (r2_hidden @ X12 @ X9)
% 0.21/0.49          | ~ (r2_hidden @ X11 @ X9))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | ~ (r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_C @ (k1_wellord2 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | ~ (r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_C @ (k1_wellord2 @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_C @ (k1_wellord2 @ X0)))
% 0.21/0.49          | ~ (r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_C @ (k1_wellord2 @ X0)))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49             (sk_C @ (k1_wellord2 @ X0))))),
% 0.21/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i]:
% 0.21/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | ~ (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.21/0.49               (sk_B @ (k1_wellord2 @ X0)))
% 0.21/0.49          | ((sk_C @ (k1_wellord2 @ X0)) = (sk_B @ (k1_wellord2 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | ((sk_C @ (k1_wellord2 @ X0)) = (sk_B @ (k1_wellord2 @ X0)))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_C @ (k1_wellord2 @ X0)) = (sk_B @ (k1_wellord2 @ X0)))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         (((sk_B @ X6) != (sk_C @ X6))
% 0.21/0.49          | (v4_relat_2 @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_wellord1])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B @ (k1_wellord2 @ X0)) != (sk_B @ (k1_wellord2 @ X0)))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B @ (k1_wellord2 @ X0)) != (sk_B @ (k1_wellord2 @ X0)))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain, (![X0 : $i]: (v4_relat_2 @ (k1_wellord2 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.49  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
