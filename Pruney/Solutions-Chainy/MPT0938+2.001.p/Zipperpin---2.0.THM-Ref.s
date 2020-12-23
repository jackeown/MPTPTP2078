%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IcTojw1Vci

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 125 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :   29
%              Number of atoms          : 1093 (1504 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( X6
       != ( k1_wellord2 @ X5 ) )
      | ( ( k3_relat_1 @ X6 )
        = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X5: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X5 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X5 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d16_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ( r8_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ~ ( r8_relat_2 @ X4 @ ( k3_relat_1 @ X4 ) )
      | ( v8_relat_2 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d8_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r8_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i,E: $i] :
              ( ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) )
             => ( r2_hidden @ ( k4_tarski @ C @ E ) @ A ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_E @ X9 @ X10 ) @ X9 )
      | ( r8_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X9 @ X10 ) @ X9 )
      | ( r8_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X9 @ X10 ) @ X9 )
      | ( r8_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X9 @ X10 ) @ X9 )
      | ( r8_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X9 @ X10 ) @ ( sk_D_1 @ X9 @ X10 ) ) @ X10 )
      | ( r8_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
       != ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('16',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('18',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','31'])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_E @ X9 @ X10 ) @ X9 )
      | ( r8_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X9 @ X10 ) @ X9 )
      | ( r8_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X9 @ X10 ) @ ( sk_E @ X9 @ X10 ) ) @ X10 )
      | ( r8_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('36',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
       != ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X6 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('56',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X5 ) )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('58',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','59'])).

thf('61',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','63'])).

thf('65',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X9 @ X10 ) @ ( sk_E @ X9 @ X10 ) ) @ X10 )
      | ( r8_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IcTojw1Vci
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 74 iterations in 0.080s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.21/0.54  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.54  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.54  thf(t3_wellord2, conjecture, (![A:$i]: ( v8_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]: ( v8_relat_2 @ ( k1_wellord2 @ A ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t3_wellord2])).
% 0.21/0.55  thf('0', plain, (~ (v8_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d1_wellord2, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.55         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.55           ( ![C:$i,D:$i]:
% 0.21/0.55             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.55               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.55                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         (((X6) != (k1_wellord2 @ X5))
% 0.21/0.55          | ((k3_relat_1 @ X6) = (X5))
% 0.21/0.55          | ~ (v1_relat_1 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X5))
% 0.21/0.55          | ((k3_relat_1 @ (k1_wellord2 @ X5)) = (X5)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.55  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.55  thf('3', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('4', plain, (![X5 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X5)) = (X5))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf(d16_relat_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( v8_relat_2 @ A ) <=> ( r8_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X4 : $i]:
% 0.21/0.55         (~ (r8_relat_2 @ X4 @ (k3_relat_1 @ X4))
% 0.21/0.55          | (v8_relat_2 @ X4)
% 0.21/0.55          | ~ (v1_relat_1 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [d16_relat_2])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (v8_relat_2 @ (k1_wellord2 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf(d8_relat_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( r8_relat_2 @ A @ B ) <=>
% 0.21/0.55           ( ![C:$i,D:$i,E:$i]:
% 0.21/0.55             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.21/0.55                 ( r2_hidden @ E @ B ) & 
% 0.21/0.55                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 0.21/0.55                 ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) =>
% 0.21/0.55               ( r2_hidden @ ( k4_tarski @ C @ E ) @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_E @ X9 @ X10) @ X9)
% 0.21/0.55          | (r8_relat_2 @ X10 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C_2 @ X9 @ X10) @ X9)
% 0.21/0.55          | (r8_relat_2 @ X10 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.21/0.55  thf(d3_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D_1 @ X9 @ X10) @ X9)
% 0.21/0.55          | (r8_relat_2 @ X10 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C_2 @ X9 @ X10) @ X9)
% 0.21/0.55          | (r8_relat_2 @ X10 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         ((r2_hidden @ 
% 0.21/0.55           (k4_tarski @ (sk_C_2 @ X9 @ X10) @ (sk_D_1 @ X9 @ X10)) @ X10)
% 0.21/0.55          | (r8_relat_2 @ X10 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (((X6) != (k1_wellord2 @ X5))
% 0.21/0.55          | ~ (r2_hidden @ X7 @ X5)
% 0.21/0.55          | ~ (r2_hidden @ X8 @ X5)
% 0.21/0.55          | (r1_tarski @ X7 @ X8)
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X6)
% 0.21/0.55          | ~ (v1_relat_1 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X5))
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k1_wellord2 @ X5))
% 0.21/0.55          | (r1_tarski @ X7 @ X8)
% 0.21/0.55          | ~ (r2_hidden @ X8 @ X5)
% 0.21/0.55          | ~ (r2_hidden @ X7 @ X5))),
% 0.21/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.55  thf('17', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k1_wellord2 @ X5))
% 0.21/0.55          | (r1_tarski @ X7 @ X8)
% 0.21/0.55          | ~ (r2_hidden @ X8 @ X5)
% 0.21/0.55          | ~ (r2_hidden @ X7 @ X5))),
% 0.21/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X1)
% 0.21/0.55          | ~ (r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_D_1 @ X1 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.55  thf('20', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X1)
% 0.21/0.55          | ~ (r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_D_1 @ X1 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | ~ (r2_hidden @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '21'])).
% 0.21/0.55  thf('23', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | ~ (r2_hidden @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_D_1 @ X0 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '25'])).
% 0.21/0.55  thf('27', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_D_1 @ X0 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55           (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r2_hidden @ X0 @ X2)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r2_hidden @ X1 @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | ~ (r2_hidden @ X1 @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.55          | (r2_hidden @ (sk_C @ X1 @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55             (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_E @ X9 @ X10) @ X9)
% 0.21/0.55          | (r8_relat_2 @ X10 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D_1 @ X9 @ X10) @ X9)
% 0.21/0.55          | (r8_relat_2 @ X10 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X9 @ X10) @ (sk_E @ X9 @ X10)) @ 
% 0.21/0.55           X10)
% 0.21/0.55          | (r8_relat_2 @ X10 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k1_wellord2 @ X5))
% 0.21/0.55          | (r1_tarski @ X7 @ X8)
% 0.21/0.55          | ~ (r2_hidden @ X8 @ X5)
% 0.21/0.55          | ~ (r2_hidden @ X7 @ X5))),
% 0.21/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X1)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | ~ (r2_hidden @ (sk_E @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_E @ X1 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('38', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X1)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | ~ (r2_hidden @ (sk_E @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_E @ X1 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_E @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | ~ (r2_hidden @ (sk_E @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['34', '39'])).
% 0.21/0.55  thf('41', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_E @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | ~ (r2_hidden @ (sk_E @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (sk_E @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_E @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_E @ X0 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['33', '43'])).
% 0.21/0.55  thf('45', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_E @ X0 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55           (sk_E @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r2_hidden @ X0 @ X2)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r2_hidden @ X1 @ (sk_E @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | ~ (r2_hidden @ X1 @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.55          | (r2_hidden @ (sk_C @ X1 @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55             (sk_E @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['32', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C @ X1 @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55           (sk_E @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_E @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | (r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55             (sk_E @ X0 @ (k1_wellord2 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55           (sk_E @ X0 @ (k1_wellord2 @ X0)))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (((X6) != (k1_wellord2 @ X5))
% 0.21/0.55          | ~ (r2_hidden @ X7 @ X5)
% 0.21/0.55          | ~ (r2_hidden @ X8 @ X5)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ X6)
% 0.21/0.55          | ~ (r1_tarski @ X7 @ X8)
% 0.21/0.55          | ~ (v1_relat_1 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X5))
% 0.21/0.55          | ~ (r1_tarski @ X7 @ X8)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k1_wellord2 @ X5))
% 0.21/0.55          | ~ (r2_hidden @ X8 @ X5)
% 0.21/0.55          | ~ (r2_hidden @ X7 @ X5))),
% 0.21/0.55      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.55  thf('57', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X7 @ X8)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k1_wellord2 @ X5))
% 0.21/0.55          | ~ (r2_hidden @ X8 @ X5)
% 0.21/0.55          | ~ (r2_hidden @ X7 @ X5))),
% 0.21/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.55          | ~ (r2_hidden @ (sk_E @ X0 @ (k1_wellord2 @ X0)) @ X1)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55              (sk_E @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55             (k1_wellord2 @ X1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['54', '58'])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55              (sk_E @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55             (k1_wellord2 @ X0))
% 0.21/0.55          | ~ (r2_hidden @ (sk_E @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '59'])).
% 0.21/0.55  thf('61', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55              (sk_E @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55             (k1_wellord2 @ X0))
% 0.21/0.55          | ~ (r2_hidden @ (sk_E @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (sk_E @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55              (sk_E @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55             (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55              (sk_E @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55             (k1_wellord2 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '63'])).
% 0.21/0.55  thf('65', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55              (sk_E @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55             (k1_wellord2 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ 
% 0.21/0.55           (k4_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.55            (sk_E @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.55           (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         (~ (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C_2 @ X9 @ X10) @ (sk_E @ X9 @ X10)) @ X10)
% 0.21/0.55          | (r8_relat_2 @ X10 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.55  thf('70', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r8_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.21/0.55          | (r8_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.55  thf('72', plain, (![X0 : $i]: (r8_relat_2 @ (k1_wellord2 @ X0) @ X0)),
% 0.21/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.21/0.55  thf('73', plain, (![X0 : $i]: (v8_relat_2 @ (k1_wellord2 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '72'])).
% 0.21/0.55  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
