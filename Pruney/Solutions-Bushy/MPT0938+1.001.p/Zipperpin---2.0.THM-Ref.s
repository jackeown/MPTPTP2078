%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0938+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QRfrsyexUk

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:45 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 114 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   26
%              Number of atoms          :  980 (1364 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X1: $i,X2: $i] :
      ( ( X2
       != ( k1_wellord2 @ X1 ) )
      | ( ( k3_relat_1 @ X2 )
        = X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X1: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d16_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ( r8_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r8_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_E @ X5 @ X6 ) @ X5 )
      | ( r8_relat_2 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( r8_relat_2 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_E @ X5 @ X6 ) @ X5 )
      | ( r8_relat_2 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X5 @ X6 ) @ X5 )
      | ( r8_relat_2 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X5 @ X6 ) @ ( sk_E @ X5 @ X6 ) ) @ X6 )
      | ( r8_relat_2 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
       != ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('15',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k1_wellord2 @ X1 ) )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X3 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('17',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k1_wellord2 @ X1 ) )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X3 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X5 @ X6 ) @ X5 )
      | ( r8_relat_2 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( r8_relat_2 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_D_1 @ X5 @ X6 ) ) @ X6 )
      | ( r8_relat_2 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('32',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k1_wellord2 @ X1 ) )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X3 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
       != ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('49',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X3 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('51',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X3 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','52'])).

thf('54',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','56'])).

thf('58',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_E @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_E @ X5 @ X6 ) ) @ X6 )
      | ( r8_relat_2 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r8_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).


%------------------------------------------------------------------------------
