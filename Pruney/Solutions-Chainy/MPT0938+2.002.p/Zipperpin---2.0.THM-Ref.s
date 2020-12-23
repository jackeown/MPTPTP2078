%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aejg5QkS5D

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 174 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   22
%              Number of atoms          :  907 (1733 expanded)
%              Number of equality atoms :   10 (  45 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t3_wellord2,conjecture,(
    ! [A: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( v8_relat_2 @ ( k1_wellord2 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t3_wellord2])).

thf('0',plain,(
    ~ ( v8_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( X12
       != ( k1_wellord2 @ X11 ) )
      | ( ( k3_relat_1 @ X12 )
        = X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X11 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X11 ) )
        = X11 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l2_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ! [B: $i,C: $i,D: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X7 ) @ ( sk_C_1 @ X7 ) ) @ X7 )
      | ( v8_relat_2 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('14',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X7 ) @ ( sk_C_1 @ X7 ) ) @ X7 )
      | ( v8_relat_2 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12
       != ( k1_wellord2 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ X11 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('16',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ ( k1_wellord2 @ X11 ) )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r2_hidden @ X14 @ X11 )
      | ~ ( r2_hidden @ X13 @ X11 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('18',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ ( k1_wellord2 @ X11 ) )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r2_hidden @ X14 @ X11 )
      | ~ ( r2_hidden @ X13 @ X11 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X11: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 ) @ ( sk_D @ X7 ) ) @ X7 )
      | ( v8_relat_2 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ X1 @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('37',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 ) @ ( sk_D @ X7 ) ) @ X7 )
      | ( v8_relat_2 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('38',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ ( k1_wellord2 @ X11 ) )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r2_hidden @ X14 @ X11 )
      | ~ ( r2_hidden @ X13 @ X11 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X11: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 ) @ ( sk_D @ X7 ) ) @ X7 )
      | ( v8_relat_2 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X5 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12
       != ( k1_wellord2 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X12 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('61',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X11 ) )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ ( k1_wellord2 @ X11 ) )
      | ~ ( r2_hidden @ X14 @ X11 )
      | ~ ( r2_hidden @ X13 @ X11 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('63',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ ( k1_wellord2 @ X11 ) )
      | ~ ( r2_hidden @ X14 @ X11 )
      | ~ ( r2_hidden @ X13 @ X11 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ X7 ) @ ( sk_D @ X7 ) ) @ X7 )
      | ( v8_relat_2 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aejg5QkS5D
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 97 iterations in 0.066s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.50  thf(t3_wellord2, conjecture, (![A:$i]: ( v8_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]: ( v8_relat_2 @ ( k1_wellord2 @ A ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t3_wellord2])).
% 0.21/0.50  thf('0', plain, (~ (v8_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d1_wellord2, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.50         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.50           ( ![C:$i,D:$i]:
% 0.21/0.50             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.50               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.50                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (((X12) != (k1_wellord2 @ X11))
% 0.21/0.50          | ((k3_relat_1 @ X12) = (X11))
% 0.21/0.50          | ~ (v1_relat_1 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X11 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k1_wellord2 @ X11))
% 0.21/0.50          | ((k3_relat_1 @ (k1_wellord2 @ X11)) = (X11)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.50  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.50  thf('3', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.50  thf('4', plain, (![X11 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X11)) = (X11))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(l2_wellord1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ( v8_relat_2 @ A ) <=>
% 0.21/0.50         ( ![B:$i,C:$i,D:$i]:
% 0.21/0.50           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 0.21/0.50               ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) =>
% 0.21/0.50             ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (k4_tarski @ (sk_B @ X7) @ (sk_C_1 @ X7)) @ X7)
% 0.21/0.50          | (v8_relat_2 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [l2_wellord1])).
% 0.21/0.50  thf(t30_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ C ) =>
% 0.21/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.50         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.50           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.21/0.50          | (r2_hidden @ X4 @ (k3_relat_1 @ X6))
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | (v8_relat_2 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | (r2_hidden @ (sk_B @ X0) @ (k3_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_B @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.50          | (v8_relat_2 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['4', '8'])).
% 0.21/0.50  thf('10', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (k4_tarski @ (sk_B @ X7) @ (sk_C_1 @ X7)) @ X7)
% 0.21/0.50          | (v8_relat_2 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [l2_wellord1])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (((X12) != (k1_wellord2 @ X11))
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X11)
% 0.21/0.50          | ~ (r2_hidden @ X14 @ X11)
% 0.21/0.50          | (r1_tarski @ X13 @ X14)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X12)
% 0.21/0.50          | ~ (v1_relat_1 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k1_wellord2 @ X11))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ (k1_wellord2 @ X11))
% 0.21/0.50          | (r1_tarski @ X13 @ X14)
% 0.21/0.50          | ~ (r2_hidden @ X14 @ X11)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X11))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf('17', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ (k1_wellord2 @ X11))
% 0.21/0.50          | (r1_tarski @ X13 @ X14)
% 0.21/0.50          | ~ (r2_hidden @ X14 @ X11)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X11))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ (sk_C_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_C_1 @ (k1_wellord2 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.50  thf('20', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ (sk_C_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_C_1 @ (k1_wellord2 @ X0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_C_1 @ (k1_wellord2 @ X0)))
% 0.21/0.50          | ~ (r2_hidden @ (sk_C_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (sk_C_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_C_1 @ (k1_wellord2 @ X0)))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.50  thf('24', plain, (![X11 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X11)) = (X11))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X7) @ (sk_D @ X7)) @ X7)
% 0.21/0.50          | (v8_relat_2 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [l2_wellord1])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.21/0.50          | (r2_hidden @ X4 @ (k3_relat_1 @ X6))
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | (v8_relat_2 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | (r2_hidden @ (sk_C_1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C_1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.50          | (v8_relat_2 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['24', '28'])).
% 0.21/0.50  thf('30', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_C_1 @ (k1_wellord2 @ X0))))),
% 0.21/0.50      inference('clc', [status(thm)], ['23', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r2_hidden @ X1 @ (sk_C_1 @ (k1_wellord2 @ X0)))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ (sk_B @ (k1_wellord2 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X1 @ (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.21/0.50             (sk_C_1 @ (k1_wellord2 @ X0)))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X7) @ (sk_D @ X7)) @ X7)
% 0.21/0.50          | (v8_relat_2 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [l2_wellord1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ (k1_wellord2 @ X11))
% 0.21/0.50          | (r1_tarski @ X13 @ X14)
% 0.21/0.50          | ~ (r2_hidden @ X14 @ X11)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X11))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ (sk_C_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (r1_tarski @ (sk_C_1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_D @ (k1_wellord2 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ (sk_C_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (r1_tarski @ (sk_C_1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_D @ (k1_wellord2 @ X0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r1_tarski @ (sk_C_1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_D @ (k1_wellord2 @ X0)))
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (r1_tarski @ (sk_C_1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_D @ (k1_wellord2 @ X0)))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.50  thf('44', plain, (![X11 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X11)) = (X11))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X7) @ (sk_D @ X7)) @ X7)
% 0.21/0.50          | (v8_relat_2 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [l2_wellord1])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.21/0.50          | (r2_hidden @ X5 @ (k3_relat_1 @ X6))
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | (v8_relat_2 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | (r2_hidden @ (sk_D @ X0) @ (k3_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.50          | (v8_relat_2 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['44', '48'])).
% 0.21/0.50  thf('50', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r1_tarski @ (sk_C_1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_D @ (k1_wellord2 @ X0))))),
% 0.21/0.50      inference('clc', [status(thm)], ['43', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r2_hidden @ X1 @ (sk_D @ (k1_wellord2 @ X0)))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ (sk_C_1 @ (k1_wellord2 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X1 @ (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.21/0.50             (sk_D @ (k1_wellord2 @ X0)))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C @ X1 @ (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.21/0.50           (sk_D @ (k1_wellord2 @ X0)))
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_D @ (k1_wellord2 @ X0)))
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50             (sk_D @ (k1_wellord2 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50           (sk_D @ (k1_wellord2 @ X0)))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (((X12) != (k1_wellord2 @ X11))
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X11)
% 0.21/0.50          | ~ (r2_hidden @ X14 @ X11)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ X13 @ X14) @ X12)
% 0.21/0.50          | ~ (r1_tarski @ X13 @ X14)
% 0.21/0.50          | ~ (v1_relat_1 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k1_wellord2 @ X11))
% 0.21/0.50          | ~ (r1_tarski @ X13 @ X14)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ X13 @ X14) @ (k1_wellord2 @ X11))
% 0.21/0.50          | ~ (r2_hidden @ X14 @ X11)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X11))),
% 0.21/0.50      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.50  thf('62', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X13 @ X14)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ X13 @ X14) @ (k1_wellord2 @ X11))
% 0.21/0.50          | ~ (r2_hidden @ X14 @ X11)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X11))),
% 0.21/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50              (sk_D @ (k1_wellord2 @ X0))) @ 
% 0.21/0.50             (k1_wellord2 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['59', '63'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50              (sk_D @ (k1_wellord2 @ X0))) @ 
% 0.21/0.50             (k1_wellord2 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '64'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50              (sk_D @ (k1_wellord2 @ X0))) @ 
% 0.21/0.50             (k1_wellord2 @ X0))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.21/0.50              (sk_D @ (k1_wellord2 @ X0))) @ 
% 0.21/0.50             (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ (sk_B @ X7) @ (sk_D @ X7)) @ X7)
% 0.21/0.50          | (v8_relat_2 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [l2_wellord1])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.50          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.50  thf('71', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v8_relat_2 @ (k1_wellord2 @ X0)) | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain, (![X0 : $i]: (v8_relat_2 @ (k1_wellord2 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['72'])).
% 0.21/0.50  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
