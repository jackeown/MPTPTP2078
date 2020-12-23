%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A6H3dhaysA

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:07 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 203 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :   24
%              Number of atoms          : 1049 (2664 expanded)
%              Number of equality atoms :   24 (  91 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9
        = ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X6 ) @ ( sk_C_1 @ X9 @ X6 ) ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X6 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k2_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k2_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X8 @ X6 ) @ X8 ) @ X6 )
      | ( X7
       != ( k2_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('6',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X8 @ X6 ) @ X8 ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 )
      | ( r2_hidden @ X21 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t47_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
             => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_relat_1])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X8 @ X6 ) @ X8 ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X15 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X15 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k2_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ sk_A )
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['37'])).

thf('39',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X8 @ X6 ) @ X8 ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('42',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X9
        = ( k2_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ ( sk_C_1 @ X9 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X6 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('48',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9
        = ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X6 ) @ ( sk_C_1 @ X9 @ X6 ) ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X6 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('50',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k2_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['46','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A6H3dhaysA
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:08:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.00/1.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.00/1.18  % Solved by: fo/fo7.sh
% 1.00/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.18  % done 969 iterations in 0.714s
% 1.00/1.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.00/1.18  % SZS output start Refutation
% 1.00/1.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.00/1.18  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.00/1.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.18  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.00/1.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.00/1.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.00/1.18  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 1.00/1.18  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.00/1.18  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.18  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.00/1.18  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.18  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.00/1.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.00/1.18  thf(d5_relat_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.00/1.18       ( ![C:$i]:
% 1.00/1.18         ( ( r2_hidden @ C @ B ) <=>
% 1.00/1.18           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.00/1.18  thf('0', plain,
% 1.00/1.18      (![X6 : $i, X9 : $i]:
% 1.00/1.18         (((X9) = (k2_relat_1 @ X6))
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X6) @ (sk_C_1 @ X9 @ X6)) @ 
% 1.00/1.18             X6)
% 1.00/1.18          | (r2_hidden @ (sk_C_1 @ X9 @ X6) @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.00/1.18  thf('1', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.00/1.18         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 1.00/1.18          | (r2_hidden @ X5 @ X7)
% 1.00/1.18          | ((X7) != (k2_relat_1 @ X6)))),
% 1.00/1.18      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.00/1.18  thf('2', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.00/1.18         ((r2_hidden @ X5 @ (k2_relat_1 @ X6))
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 1.00/1.18      inference('simplify', [status(thm)], ['1'])).
% 1.00/1.18  thf('3', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 1.00/1.18          | ((X1) = (k2_relat_1 @ X0))
% 1.00/1.18          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['0', '2'])).
% 1.00/1.18  thf(d3_tarski, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( r1_tarski @ A @ B ) <=>
% 1.00/1.18       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.00/1.18  thf('4', plain,
% 1.00/1.18      (![X1 : $i, X3 : $i]:
% 1.00/1.18         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 1.00/1.18  thf('5', plain,
% 1.00/1.18      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.00/1.18         (~ (r2_hidden @ X8 @ X7)
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X8 @ X6) @ X8) @ X6)
% 1.00/1.18          | ((X7) != (k2_relat_1 @ X6)))),
% 1.00/1.18      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.00/1.18  thf('6', plain,
% 1.00/1.18      (![X6 : $i, X8 : $i]:
% 1.00/1.18         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X8 @ X6) @ X8) @ X6)
% 1.00/1.18          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X6)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['5'])).
% 1.00/1.18  thf('7', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 1.00/1.18              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 1.00/1.18             X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['4', '6'])).
% 1.00/1.18  thf(t20_relat_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ C ) =>
% 1.00/1.18       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 1.00/1.18         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.00/1.18           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 1.00/1.18  thf('8', plain,
% 1.00/1.18      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.00/1.18         (~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23)
% 1.00/1.18          | (r2_hidden @ X21 @ (k1_relat_1 @ X23))
% 1.00/1.18          | ~ (v1_relat_1 @ X23))),
% 1.00/1.18      inference('cnf', [status(esa)], [t20_relat_1])).
% 1.00/1.18  thf('9', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 1.00/1.18             (k1_relat_1 @ X0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['7', '8'])).
% 1.00/1.18  thf(t47_relat_1, conjecture,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ![B:$i]:
% 1.00/1.18         ( ( v1_relat_1 @ B ) =>
% 1.00/1.18           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.00/1.18             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.00/1.18  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.18    (~( ![A:$i]:
% 1.00/1.18        ( ( v1_relat_1 @ A ) =>
% 1.00/1.18          ( ![B:$i]:
% 1.00/1.18            ( ( v1_relat_1 @ B ) =>
% 1.00/1.18              ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.00/1.18                ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 1.00/1.18    inference('cnf.neg', [status(esa)], [t47_relat_1])).
% 1.00/1.18  thf('10', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('11', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (~ (r2_hidden @ X0 @ X1)
% 1.00/1.18          | (r2_hidden @ X0 @ X2)
% 1.00/1.18          | ~ (r1_tarski @ X1 @ X2))),
% 1.00/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 1.00/1.18  thf('12', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 1.00/1.18          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_A)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['10', '11'])).
% 1.00/1.18  thf('13', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ sk_A)
% 1.00/1.18          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.00/1.18          | (r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 1.00/1.18             (k2_relat_1 @ sk_B)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['9', '12'])).
% 1.00/1.18  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('15', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.00/1.18          | (r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 1.00/1.18             (k2_relat_1 @ sk_B)))),
% 1.00/1.18      inference('demod', [status(thm)], ['13', '14'])).
% 1.00/1.18  thf('16', plain,
% 1.00/1.18      (![X6 : $i, X8 : $i]:
% 1.00/1.18         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X8 @ X6) @ X8) @ X6)
% 1.00/1.18          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X6)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['5'])).
% 1.00/1.18  thf('17', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ 
% 1.00/1.18              (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 1.00/1.18               sk_B) @ 
% 1.00/1.18              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_A)) @ sk_A)) @ 
% 1.00/1.18             sk_B))),
% 1.00/1.18      inference('sup-', [status(thm)], ['15', '16'])).
% 1.00/1.18  thf('18', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 1.00/1.18              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 1.00/1.18             X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['4', '6'])).
% 1.00/1.18  thf(dt_k5_relat_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.00/1.18       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.00/1.18  thf('19', plain,
% 1.00/1.18      (![X19 : $i, X20 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X19)
% 1.00/1.18          | ~ (v1_relat_1 @ X20)
% 1.00/1.18          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 1.00/1.18      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.00/1.18  thf(d8_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ![B:$i]:
% 1.00/1.18         ( ( v1_relat_1 @ B ) =>
% 1.00/1.18           ( ![C:$i]:
% 1.00/1.18             ( ( v1_relat_1 @ C ) =>
% 1.00/1.18               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 1.00/1.18                 ( ![D:$i,E:$i]:
% 1.00/1.18                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 1.00/1.18                     ( ?[F:$i]:
% 1.00/1.18                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 1.00/1.18                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 1.00/1.18  thf('20', plain,
% 1.00/1.18      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X11)
% 1.00/1.18          | ((X13) != (k5_relat_1 @ X12 @ X11))
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ X13)
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X12)
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X16 @ X15) @ X11)
% 1.00/1.18          | ~ (v1_relat_1 @ X13)
% 1.00/1.18          | ~ (v1_relat_1 @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [d8_relat_1])).
% 1.00/1.18  thf('21', plain,
% 1.00/1.18      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X12)
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X16 @ X15) @ X11)
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X12)
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ (k5_relat_1 @ X12 @ X11))
% 1.00/1.18          | ~ (v1_relat_1 @ X11))),
% 1.00/1.18      inference('simplify', [status(thm)], ['20'])).
% 1.00/1.18  thf('22', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X1))),
% 1.00/1.18      inference('sup-', [status(thm)], ['19', '21'])).
% 1.00/1.18  thf('23', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.18         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ X0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['22'])).
% 1.00/1.18  thf('24', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X2)
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 1.00/1.18             (k5_relat_1 @ X2 @ X0))
% 1.00/1.18          | ~ (r2_hidden @ 
% 1.00/1.18               (k4_tarski @ X3 @ 
% 1.00/1.18                (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) @ 
% 1.00/1.18               X2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['18', '23'])).
% 1.00/1.18  thf('25', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ 
% 1.00/1.18              (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 1.00/1.18               sk_B) @ 
% 1.00/1.18              (sk_C @ X0 @ (k2_relat_1 @ sk_A))) @ 
% 1.00/1.18             (k5_relat_1 @ sk_B @ sk_A))
% 1.00/1.18          | ~ (v1_relat_1 @ sk_B)
% 1.00/1.18          | ~ (v1_relat_1 @ sk_A)
% 1.00/1.18          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['17', '24'])).
% 1.00/1.18  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('28', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ 
% 1.00/1.18              (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 1.00/1.18               sk_B) @ 
% 1.00/1.18              (sk_C @ X0 @ (k2_relat_1 @ sk_A))) @ 
% 1.00/1.18             (k5_relat_1 @ sk_B @ sk_A))
% 1.00/1.18          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 1.00/1.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.00/1.18  thf('29', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r2_hidden @ 
% 1.00/1.18           (k4_tarski @ 
% 1.00/1.18            (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 1.00/1.18             sk_B) @ 
% 1.00/1.18            (sk_C @ X0 @ (k2_relat_1 @ sk_A))) @ 
% 1.00/1.18           (k5_relat_1 @ sk_B @ sk_A))
% 1.00/1.18          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['28'])).
% 1.00/1.18  thf('30', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.00/1.18         ((r2_hidden @ X5 @ (k2_relat_1 @ X6))
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 1.00/1.18      inference('simplify', [status(thm)], ['1'])).
% 1.00/1.18  thf('31', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.00/1.18          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_A)) @ 
% 1.00/1.18             (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['29', '30'])).
% 1.00/1.18  thf('32', plain,
% 1.00/1.18      (![X1 : $i, X3 : $i]:
% 1.00/1.18         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 1.00/1.18  thf('33', plain,
% 1.00/1.18      (((r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 1.00/1.18         (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))
% 1.00/1.18        | (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 1.00/1.18           (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['31', '32'])).
% 1.00/1.18  thf('34', plain,
% 1.00/1.18      ((r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 1.00/1.18        (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['33'])).
% 1.00/1.18  thf('35', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (~ (r2_hidden @ X0 @ X1)
% 1.00/1.18          | (r2_hidden @ X0 @ X2)
% 1.00/1.18          | ~ (r1_tarski @ X1 @ X2))),
% 1.00/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 1.00/1.18  thf('36', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r2_hidden @ X0 @ (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))
% 1.00/1.18          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['34', '35'])).
% 1.00/1.18  thf('37', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_A) @ X0) @ (k2_relat_1 @ X0))
% 1.00/1.18          | ((k2_relat_1 @ sk_A) = (k2_relat_1 @ X0))
% 1.00/1.18          | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_A) @ X0) @ 
% 1.00/1.18             (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['3', '36'])).
% 1.00/1.18  thf('38', plain,
% 1.00/1.18      ((((k2_relat_1 @ sk_A) = (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))
% 1.00/1.18        | (r2_hidden @ 
% 1.00/1.18           (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18           (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.18      inference('eq_fact', [status(thm)], ['37'])).
% 1.00/1.18  thf('39', plain,
% 1.00/1.18      (((k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) != (k2_relat_1 @ sk_A))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('40', plain,
% 1.00/1.18      ((r2_hidden @ 
% 1.00/1.18        (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18        (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))),
% 1.00/1.18      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 1.00/1.18  thf('41', plain,
% 1.00/1.18      (![X6 : $i, X8 : $i]:
% 1.00/1.18         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X8 @ X6) @ X8) @ X6)
% 1.00/1.18          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X6)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['5'])).
% 1.00/1.18  thf('42', plain,
% 1.00/1.18      ((r2_hidden @ 
% 1.00/1.18        (k4_tarski @ 
% 1.00/1.18         (sk_D_1 @ 
% 1.00/1.18          (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18          (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18         (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A))) @ 
% 1.00/1.18        (k5_relat_1 @ sk_B @ sk_A))),
% 1.00/1.18      inference('sup-', [status(thm)], ['40', '41'])).
% 1.00/1.18  thf('43', plain,
% 1.00/1.18      (![X6 : $i, X9 : $i, X10 : $i]:
% 1.00/1.18         (((X9) = (k2_relat_1 @ X6))
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X10 @ (sk_C_1 @ X9 @ X6)) @ X6)
% 1.00/1.18          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X6) @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.00/1.18  thf('44', plain,
% 1.00/1.18      ((~ (r2_hidden @ 
% 1.00/1.18           (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18           (k2_relat_1 @ sk_A))
% 1.00/1.18        | ((k2_relat_1 @ sk_A) = (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['42', '43'])).
% 1.00/1.18  thf('45', plain,
% 1.00/1.18      (((k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) != (k2_relat_1 @ sk_A))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('46', plain,
% 1.00/1.18      (~ (r2_hidden @ 
% 1.00/1.18          (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18          (k2_relat_1 @ sk_A))),
% 1.00/1.18      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 1.00/1.18  thf('47', plain,
% 1.00/1.18      (![X19 : $i, X20 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X19)
% 1.00/1.18          | ~ (v1_relat_1 @ X20)
% 1.00/1.18          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 1.00/1.18      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.00/1.18  thf('48', plain,
% 1.00/1.18      (![X6 : $i, X9 : $i]:
% 1.00/1.18         (((X9) = (k2_relat_1 @ X6))
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X6) @ (sk_C_1 @ X9 @ X6)) @ 
% 1.00/1.18             X6)
% 1.00/1.18          | (r2_hidden @ (sk_C_1 @ X9 @ X6) @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.00/1.18  thf('49', plain,
% 1.00/1.18      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X17 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X11)
% 1.00/1.18          | ((X13) != (k5_relat_1 @ X12 @ X11))
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ (sk_F_1 @ X17 @ X14 @ X11 @ X12) @ X17) @ X11)
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ X13)
% 1.00/1.18          | ~ (v1_relat_1 @ X13)
% 1.00/1.18          | ~ (v1_relat_1 @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [d8_relat_1])).
% 1.00/1.18  thf('50', plain,
% 1.00/1.18      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X12)
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ (sk_F_1 @ X17 @ X14 @ X11 @ X12) @ X17) @ X11)
% 1.00/1.18          | ~ (v1_relat_1 @ X11))),
% 1.00/1.18      inference('simplify', [status(thm)], ['49'])).
% 1.00/1.18  thf('51', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X2)
% 1.00/1.18          | ((X2) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ 
% 1.00/1.18              (sk_F_1 @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.00/1.18               (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.00/1.18              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 1.00/1.18             X0)
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ X1))),
% 1.00/1.18      inference('sup-', [status(thm)], ['48', '50'])).
% 1.00/1.18  thf('52', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ 
% 1.00/1.18              (sk_F_1 @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.00/1.18               (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.00/1.18              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 1.00/1.18             X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | ((X2) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.00/1.18          | (r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['47', '51'])).
% 1.00/1.18  thf('53', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X2)
% 1.00/1.18          | ((X2) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.00/1.18          | (r2_hidden @ 
% 1.00/1.18             (k4_tarski @ 
% 1.00/1.18              (sk_F_1 @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.00/1.18               (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.00/1.18              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 1.00/1.18             X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ X0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['52'])).
% 1.00/1.18  thf('54', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.00/1.18         ((r2_hidden @ X5 @ (k2_relat_1 @ X6))
% 1.00/1.18          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 1.00/1.18      inference('simplify', [status(thm)], ['1'])).
% 1.00/1.18  thf('55', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ((X2) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.00/1.18          | (r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X2)
% 1.00/1.18          | (r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.00/1.18             (k2_relat_1 @ X0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['53', '54'])).
% 1.00/1.18  thf('56', plain,
% 1.00/1.18      (~ (r2_hidden @ 
% 1.00/1.18          (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18          (k2_relat_1 @ sk_A))),
% 1.00/1.18      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 1.00/1.18  thf('57', plain,
% 1.00/1.18      (((r2_hidden @ 
% 1.00/1.18         (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18         (k2_relat_1 @ sk_A))
% 1.00/1.18        | ((k2_relat_1 @ sk_A) = (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))
% 1.00/1.18        | ~ (v1_relat_1 @ sk_B)
% 1.00/1.18        | ~ (v1_relat_1 @ sk_A))),
% 1.00/1.18      inference('sup-', [status(thm)], ['55', '56'])).
% 1.00/1.18  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('60', plain,
% 1.00/1.18      (((r2_hidden @ 
% 1.00/1.18         (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18         (k2_relat_1 @ sk_A))
% 1.00/1.18        | ((k2_relat_1 @ sk_A) = (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))),
% 1.00/1.18      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.00/1.18  thf('61', plain,
% 1.00/1.18      (((k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) != (k2_relat_1 @ sk_A))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('62', plain,
% 1.00/1.18      ((r2_hidden @ 
% 1.00/1.18        (sk_C_1 @ (k2_relat_1 @ sk_A) @ (k5_relat_1 @ sk_B @ sk_A)) @ 
% 1.00/1.18        (k2_relat_1 @ sk_A))),
% 1.00/1.18      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 1.00/1.18  thf('63', plain, ($false), inference('demod', [status(thm)], ['46', '62'])).
% 1.00/1.18  
% 1.00/1.18  % SZS output end Refutation
% 1.00/1.18  
% 1.00/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
